package edu.boisestate.datagen;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.rmi.AlreadyBoundException;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import org.tinylog.Logger;

import com.github.difflib.DiffUtils;
import com.github.difflib.patch.Patch;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.codegen.Codegen;
import edu.boisestate.datagen.instrumenters.IfStatementInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.instrumenters.TestCaseInstrumenter;
import edu.boisestate.datagen.instrumenters.Wrapper;
import edu.boisestate.datagen.reporting.Record;
import edu.boisestate.datagen.rmi.DataPointServerImpl;
import edu.boisestate.datagen.server.Cache;
import edu.boisestate.datagen.utils.Compiler;
import edu.boisestate.datagen.utils.FileOps;
import net.sourceforge.argparse4j.ArgumentParsers;
import net.sourceforge.argparse4j.inf.ArgumentParser;
import net.sourceforge.argparse4j.inf.ArgumentParserException;
import net.sourceforge.argparse4j.inf.Namespace;

public class App {
    private static String workdir;
    private static String source;
    private static String compiledPath;
    private static String augmentedPath;
    private static String reportingPath;
    private static String checkpointPath;
    private static String evosuiteJarPath;
    private static String junitJarPath;
    private static String daikonJarPath;

    private static int iteration;

    public static void main(String[] args) {
        // Arguments:
        // 1. The path to the source code file(s), This is a folder.
        // 2. Workdir. This is a folder where datagen works.
        // - A {{workdir}}/instrumented/augmented contains the instrumented code with
        // augmentations.
        // - A {{workdir}}/instrumented/reporting contains the code that will report the
        // data to our lib.
        // - A {{workdir}}/compiled/ contains the compiled instrumented code.

        ArgumentParser argParser = ArgumentParsers.newFor("datagen").build()
                .description("DataGen is a tool for generating data-driven tests for Java programs.");

        argParser.addArgument("-s", "--source")
                .help("The path to the source code file(s), This is a folder.")
                .required(true)
                .type(String.class);

        argParser.addArgument("-w", "--workdir")
                .help("Working directory for datagen.")
                .required(true)
                .type(String.class);

        argParser.addArgument("-e", "--evosuite")
                .help("Evosuite jar file.")
                .required(false)
                .type(String.class);

        argParser.addArgument("-j", "--junit")
                .help("JUnit jar file path. This should also contain the hamcrest jar.")
                .required(false)
                .type(String.class);

        argParser.addArgument("-d", "--daikon")
                .help("Daikon jar file path.")
                .required(false)
                .type(String.class);

        // Parse arguments.
        try {
            Namespace ns = argParser.parseArgs(args);
            source = ns.getString("source");
            workdir = ns.getString("workdir");
            evosuiteJarPath = evosuitePresentInClassPath().orElse(ns.getString("evosuite"));
            junitJarPath = isJunitPresentInClassPath().orElse(ns.getString("junit"));
            daikonJarPath = getJarFromClassPath("daikon").orElse(ns.getString("daikon"));

        } catch (ArgumentParserException e) {
            argParser.handleError(e);
            System.exit(1);
        }

        // Start the DataPointServer.
        try {
            DataPointServerImpl dpServer = new DataPointServerImpl();
            dpServer.start();
        } catch (AlreadyBoundException e) {
            System.err.println("Could not start datapointserverimpl.");
            e.printStackTrace();
        } catch (RemoteException e) {
            System.err.println("Could not start datapointserverimpl - RemoteException.");
            e.printStackTrace();
        }

        // Check classpaths for evosuite and junit.
        if (evosuiteJarPath == null || junitJarPath == null || daikonJarPath == null) {
            System.err.println(
                    "Evosuite, JUnit, or Daikon jar file not provided, and evosuite, junit, or daikon is not present in the classpath.");
            // Print out the status of the jars.
            if (!(evosuiteJarPath == null))
                System.err.println("Evosuite jar: " + evosuiteJarPath);
            if (!(junitJarPath == null))
                System.err.println("JUnit jar: " + junitJarPath);
            if (!(daikonJarPath == null))
                System.err.println("Daikon jar: " + daikonJarPath);
            System.err.println(
                    "Use the -e, -j, and -d flags to provide the evosuite, junit, and daikon jar paths respectively.");
            System.exit(1);
        }

        // Ensure the source path is a directory, and it exists.
        File sourceDir = new File(source);
        if (!sourceDir.exists() || !sourceDir.isDirectory()) {
            Logger.error("Source path does not exist or is not a directory.");
            System.exit(1);
        }

        // Create working directory structure.
        augmentedPath = workdir + "/instrumented/augmented";
        reportingPath = workdir + "/instrumented/reporting";
        compiledPath = workdir + "/compiled";
        checkpointPath = workdir + "/checkpoint";

        FileOps.createDirectory(augmentedPath);
        FileOps.createDirectory(reportingPath);
        FileOps.createDirectory(compiledPath);
        FileOps.createDirectory(checkpointPath);

        File evosuiteTests = new File("./evosuite-tests");

        // Setup classpaths.
        ArrayList<String> classpathsList = new ArrayList<>();
        classpathsList.add(compiledPath);
        classpathsList.add(reportingPath);
        classpathsList.add(checkpointPath);
        classpathsList.add(sourceDir.getAbsolutePath());
        classpathsList.addAll(Arrays.asList(getDatagenClassPath()));
        classpathsList.addAll(Arrays.asList(evosuiteJarPath, junitJarPath));
        classpathsList.add(evosuiteTests.getAbsolutePath());

        String[] classpaths = classpathsList.toArray(new String[] {});

        Logger.info("Starting datagen.");

        // Main loop.
        do {
            // Time the iteration.
            long startTime = System.currentTimeMillis();

            // Copy the source code to the augmented and reporting folders.
            FileOps.recursivelyCopyFolder(sourceDir, new File(augmentedPath));
            FileOps.recursivelyCopyFolder(sourceDir, new File(reportingPath));

            // Initialize parsers and general instrumenters.
            JavaParser parser = new JavaParser();
            ImportInstrumenter importInstrumenter = new ImportInstrumenter();
            IfStatementInstrumenter ifInstrumenterInstrumentation = new IfStatementInstrumenter(
                    InstrumentationMode.INSTRUMENTATION);
            Wrapper wrappingInstrumenter = new Wrapper();

            // Add imports and reporting code to the branches.
            File[] reportingFiles = (new File(reportingPath)).listFiles(file -> file.getName().endsWith(".java"));
            for (File reportingFile : reportingFiles) {
                // For files in the reporting path, we add imports and reporting code.
                // to the branches.
                CompilationUnit cu = parser.parse(FileOps.readFile(reportingFile)).getResult().orElseThrow();

                cu.findAll(CompilationUnit.class).stream().forEach(importInstrumenter::instrument);
                cu.findAll(CompilationUnit.class).stream().forEach(ifInstrumenterInstrumentation::instrument);

                try {
                    FileWriter fw = new FileWriter(reportingFile.getAbsolutePath());
                    fw.write(cu.toString());
                    fw.close();

                } catch (IOException e) {
                    e.printStackTrace();
                    System.exit(1);
                }
            }

            // Augment branches and loops.
            File[] augmentedFiles = (new File(augmentedPath)).listFiles(file -> file.getName().endsWith(".java"));
            for (File augmentedFile : augmentedFiles) {
                File file = new File(augmentedFile.getAbsolutePath());
                String contents = FileOps.readFile(file);
                CompilationUnit cu = parser.parse(contents).getResult().orElseThrow();
                IfStatementInstrumenter ifStatementInstrumenterAugmentation = new IfStatementInstrumenter(
                        InstrumentationMode.AUGMENTATION);

                // We need to wrap all our branches and loops with the wrapping instrumenter.
                cu.findAll(CompilationUnit.class).stream().forEach(wrappingInstrumenter::instrument);
                cu.findAll(CompilationUnit.class).stream().forEach(ifStatementInstrumenterAugmentation::instrument);

                try {
                    FileWriter fw = new FileWriter(augmentedFile.getAbsolutePath());
                    fw.write(cu.toString());
                    fw.close();

                } catch (IOException e) {
                    e.printStackTrace();
                    System.exit(1);
                }
            }
            System.out.println(); // Makes segments readable.
            Logger.info("---------------- Iteration " + ++iteration + " ----------------");
            Logger.info("Creating checkpoint folder for iteration " + iteration);

            String checkpointFolder = (checkpointPath + File.separator + iteration);
            FileOps.createDirectory(checkpointFolder);
            Logger.debug("Checkpoint folder created at " + checkpointFolder);

            // Each file in the augmented folder is compiled and put in the compiled folder.
            for (File javaFile : ((new File(augmentedPath)).listFiles(file -> file.getName().endsWith(".java")))) {
                File file = new File(javaFile.getAbsolutePath());
                Compiler.compile(file.getAbsolutePath(), compiledPath, classpaths);
            }

            // List all compiled files in the compiled folder.
            File compiledFiles = new File(compiledPath);
            File[] javaFilesCompiled = compiledFiles.listFiles(file -> file.getName().endsWith(".class"));

            // Time.
            long startTimeEvosuite = System.currentTimeMillis();
            // Run evosuite on each compiled file.
            for (File javaFile : javaFilesCompiled) {
                File file = new File(javaFile.getAbsolutePath());
                String className = file.getName().substring(0, file.getName().length() - 6);

                // Build a prcess builder to run evosuite.
                ProcessBuilder pb = new ProcessBuilder("java", "-jar", evosuiteJarPath, "-projectCP",
                        compiledFiles.getAbsolutePath(),
                        "-class", className, "-Dcriterion=BRANCH");

                pb.redirectErrorStream(true);
                try {
                    Logger.info("Running evosuite on " + className);
                    Process p = pb.start();
                    // print the output of the process
                    BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
                    String line;
                    StringBuilder sb = new StringBuilder();
                    while ((line = reader.readLine()) != null) {
                        sb.append(line);
                    }
                    p.waitFor();

                    Logger.debug("Evosuite finished running on " + className);
                    // Check the exit code of the process.
                    if (p.exitValue() != 0) {
                        Logger.error("Evosuite exited with non-zero exit code.");
                        Logger.error("Evosuite output:");
                        Logger.error(sb.toString());
                        System.exit(1);
                    }

                } catch (IOException | InterruptedException e) {
                    e.printStackTrace();
                    System.exit(1);
                }
            }
            long endTimeEvosuite = System.currentTimeMillis();
            long elapsedTimeEvosuite = endTimeEvosuite - startTimeEvosuite;
            Logger.info("Evosuite finished running on " + javaFilesCompiled.length + " files in " + elapsedTimeEvosuite
                    + " milliseconds.");

            // Now, instrument the evosuite testcases with method invocation
            // instrumentation. Evosuite tests are generated in the $PWD/evosuite-tests
            // folder.

            File[] evosuiteTestsFiles = evosuiteTests.listFiles(file -> file.getName().endsWith("_ESTest.java"));
            if (evosuiteTestsFiles == null) {
                System.err.println("No evosuite tests were generated.");
                System.exit(1);
            }

            // Instrument the evosuite test file with method invocation.
            for (File evosuiteTestFile : evosuiteTestsFiles) {
                // Because evosuite generates some scaffolding files, we only want to
                // instrument the actual test files.
                String contents = FileOps.readFile(evosuiteTestFile);
                CompilationUnit cu = parser.parse(contents).getResult().orElseThrow();
                // Run the instrumentation on the evosuite test files.
                cu.findAll(CompilationUnit.class).stream().forEach(new ImportInstrumenter()::instrument);
                cu.findAll(CompilationUnit.class).stream().forEach(new TestCaseInstrumenter()::instrument);

                String modifiedSource = cu.toString();
                FileOps.writeFile(evosuiteTestFile, modifiedSource);
            }
            // Save the instrumented evosuite tests in the checkpoint folder.
            FileOps.recursivelyCopyFolder(evosuiteTests, new File(checkpointFolder));

            // Compile the instrumented evosuite test files along with the compiled files
            // from the source directory.
            for (File evosuiteTestFile : evosuiteTestsFiles) {
                File file = new File(evosuiteTestFile.getAbsolutePath());
                Compiler.compile(file.getAbsolutePath(), compiledPath, classpaths);
            }

            // Run evosuite tests on the files generated in the compiled folder, so that
            // we can get reported data points from them.
            // In order to use the reporting code, we will first need to compile the
            // "reporting" dir
            // into the compiled folder (as opposed to the augmented files), because
            // augmented files
            // do not report data points.
            reportingFiles = new File(reportingPath).listFiles(file -> file.getName().endsWith(".java"));
            for (File reportingFile : reportingFiles) {
                Compiler.compile(reportingFile.getAbsolutePath(), compiledPath, classpaths);
            }

            // Run JUnit.
            for (File evosuiteTestFile : (new File(compiledPath))
                    .listFiles(file -> file.getName().endsWith("_ESTest.class"))) {
                String[] command = {
                        "java",
                        "-cp",
                        String.join(File.pathSeparator, classpaths),
                        "org.junit.runner.JUnitCore",
                        evosuiteTestFile.getName().substring(0, evosuiteTestFile.getName().length() - 6),
                };

                ProcessBuilder pb = new ProcessBuilder(command);
                pb.redirectErrorStream(true);
                try {
                    Logger.info("Running JUnit tests from " + evosuiteTestFile.getName());
                    Process p = pb.start();
                    // print the output of the process
                    BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
                    String line;
                    StringBuilder sb = new StringBuilder();
                    while ((line = reader.readLine()) != null) {
                        sb.append(line);
                    }
                    p.waitFor();
                    // Check the exit code of the process.
                    if (p.exitValue() != 0) {
                        System.err.println("JUnit exited with non-zero exit code. Exit code: " +
                                p.exitValue());
                        System.err.println("JUnit output:");
                        System.err.println(sb.toString());
                        System.exit(1);
                    }
                } catch (IOException | InterruptedException e) {
                    System.err.println("Could not run junit");
                    e.printStackTrace();
                    System.exit(1);
                }
            }

            // Make a directory to store the code.
            String codefolder = checkpointFolder + File.separator + "code";
            FileOps.createDirectory(codefolder);

            // Generate code.
            Codegen.generateCode(codefolder);

            // Run daikon on the generated code.
            // The compilation directory should be cleared now. We do not need it anymore.
            // Since we have trace files, we just need to compile them, and the original
            // source code files into the compiled folder (it contains the
            // instrumented+compiled source code).
            // at this point.
            FileOps.recursivelyDeleteFolder(new File(compiledPath));

            // Compile the files in the source directory into the compiled folder.
            for (File javaFile : ((new File(source)).listFiles(file -> file.getName().endsWith(".java")))) {
                File file = new File(javaFile.getAbsolutePath());
                Compiler.compile(file.getAbsolutePath(), compiledPath, classpaths);
            }

            // Now finally, we can compile the trace files.
            for (File file : (new File(codefolder)).listFiles(file -> file.getName().endsWith(".java"))) {
                Compiler.compile(file.getAbsolutePath(), compiledPath, classpaths);
            }

            // NOW we can run daikon on the generated code.
            // Go back to the compiled folder, and find all class files that start with
            // DAIKONTEST_.
            File[] daikonTestFiles = (new File(compiledPath))
                    .listFiles(file -> file.getName().startsWith("DAIKONTEST_"));
            for (File daikonTestFile : daikonTestFiles) {
                String[] command_dyncomp = {
                        "java",
                        "-cp",
                        String.join(File.pathSeparator, classpaths),
                        "daikon.DynComp",
                        daikonTestFile.getName().substring(0, daikonTestFile.getName().length() - 6),
                };

                ProcessBuilder pb = new ProcessBuilder(command_dyncomp);
                pb.redirectErrorStream(true);
                try {
                    Logger.info("Running Daikon tests from " + daikonTestFile.getName());
                    Process p = pb.start();
                    // print the output of the process
                    BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
                    String line;
                    StringBuilder sb = new StringBuilder();
                    while ((line = reader.readLine()) != null) {
                        sb.append(line);
                    }
                    p.waitFor();

                    // Check the exit code of the process.
                    if (p.exitValue() != 0) {
                        System.err.println("Daikon exited with non-zero exit code. Exit code: " +
                                p.exitValue());
                        System.err.println("Daikon output:");
                        System.err.println(sb.toString());
                        System.exit(1);
                    }
                } catch (IOException | InterruptedException e) {
                    System.err.println("Could not run Daikon");
                    e.printStackTrace();
                    System.exit(1);
                }

                // Run daikon chicory on it next, capture the output and save it as an invariant
                // file.
                String[] command_chicory = {
                        "java",
                        "-cp",
                        String.join(File.pathSeparator, classpaths),
                        "daikon.Chicory",
                        "--daikon",
                        String.format("--comparability-file=%s.decls-DynComp",
                                daikonTestFile.getName().substring(0, daikonTestFile.getName().length() - 6)),
                        daikonTestFile.getName().substring(0, daikonTestFile.getName().length() - 6),
                };

                ProcessBuilder pb_chicory = new ProcessBuilder(command_chicory);
                pb_chicory.redirectErrorStream(true);
                try {
                    Process p_chicory = pb_chicory.start();
                    // print the output of the process
                    BufferedReader reader_chicory = new BufferedReader(
                            new InputStreamReader(p_chicory.getInputStream()));
                    String line_chicory;
                    StringBuilder sb_chicory = new StringBuilder();
                    while ((line_chicory = reader_chicory.readLine()) != null) {
                        sb_chicory.append(line_chicory);
                        sb_chicory.append("\n");
                    }
                    p_chicory.waitFor();

                    // Check the exit code of the process.
                    if (p_chicory.exitValue() != 0) {
                        System.err.println("Daikon Chicory exited with non-zero exit code. Exit code: " +
                                p_chicory.exitValue());
                        System.err.println("Daikon Chicory output:");
                        System.err.println(sb_chicory.toString());
                        System.exit(1);
                    }

                    // Save the output of the chicory run as an invariant file in the code/
                    // directory with
                    // an exgtension of ".inv".
                    File invariantFile = new File(codefolder + File.separator
                            + daikonTestFile.getName().substring(0, daikonTestFile.getName().length() - 6) + ".inv");
                    FileOps.writeFile(invariantFile, sb_chicory.toString());
                } catch (IOException | InterruptedException e) {
                    System.err.println("Could not run Daikon Chicory");
                    e.printStackTrace();
                    System.exit(1);
                }
            }

            // Wipe out the augmented, reporting, and compiled folders for the next
            // iteration.
            FileOps.recursivelyDeleteFolder(new File(augmentedPath));
            FileOps.recursivelyDeleteFolder(new File(reportingPath));
            FileOps.recursivelyDeleteFolder(new File(compiledPath));

            long endTime = System.currentTimeMillis();
            long elapsedTime = endTime - startTime;
            Logger.debug("Iteration " + iteration + " took " + elapsedTime + " milliseconds.");

            Logger.info("Dumping variable values for usage with DIG tool.");
            // get the traces from the Cache, and dump them to a CSV file.
            // True and false traces are dumped separately.
            // Create a dump folder, like the code folder.
            FileOps.createDirectory(checkpointPath + File.separator + iteration + File.separator + "vtracedump");
            for (String pathKey : Cache.getInstance().dataCache.keySet()) {
                // Get the data for this path key.
                ArrayList<Record> data = Cache.getInstance().dataCache.get(pathKey);

                // Data contains multiple data points. The structure to dump it is like this:
                // vtrace{iteration}; I var1; I var2; I var3; ... <- This is the header that DIG
                // expects.
                // vtrace{iteration}; p1; p2; p3; ... <- This is the data that DIG expects, p1,
                // p2, p3 are values of
                // var1, var2, var3, respectively.
                // We need to dump the data in the format that DIG expects.
                StringBuilder sb = new StringBuilder();
                sb.append("vtrace" + iteration + ";");

                // Get variable names. and generate the header.
                // All traces have the same variable names, so we should be safe.
                for (String varname: data.get(0).trace.keySet()) {
                    sb.append("I " + varname + ";");
                }

                sb.append("\n");

                // now append the data.
                for (Record record : data) {
                    sb.append("vtrace" + iteration + ";");
                    for (String varname: record.trace.keySet()) {
                        sb.append(record.trace.get(varname) + ";");
                    }
                    sb.append("\n");
                }

                // Sanitize the path key for filesystem.
                pathKey = pathKey.replaceAll("\\W", "_");
                FileOps.writeFile(new File(checkpointPath + File.separator + iteration + File.separator + "vtracedump"
                        + File.separator + pathKey + ".csv"), sb.toString());
            }

            if (iteration == 1)
                continue;
            else {
                // Check the last iteration's output for determining the fixed point.
                // First, find the last iteration's code folder.
                File lastIterationCodeFolder = new File(
                        checkpointPath + File.separator + (iteration - 1) + File.separator + "code");

                // List all invariant files (have the extension ".inv") in the last iteration's
                // code folder.
                File[] invariantFiles = lastIterationCodeFolder.listFiles(file -> file.getName().endsWith(".inv"));

                if (invariantFiles.length == 0) {
                    Logger.error("No invariant files found in the last iteration's code folder.");
                    continue;
                }

                // Count the number of files for which we have reached a fixed point.
                int fixedFiles = 0;
                // For each invariant file, check if it is present in the current iteration's
                // code folder.
                for (File invariantFile : invariantFiles) {
                    File currentIterationInvariantFile = new File(
                            codefolder + File.separator + invariantFile.getName());
                    if (!currentIterationInvariantFile.exists()) {
                        Logger.error("Invariant file " + invariantFile.getName()
                                + " not found in the current iteration's code folder.");
                        continue;
                    } else {
                        // Compare the contents of the last invariant file with the current invariant
                        // file.
                        // Read each file into a list of strings (lines).
                        List<String> lastInvariantFileLines = FileOps.readFileLines(invariantFile);
                        List<String> currentInvariantFileLines = FileOps.readFileLines(currentIterationInvariantFile);

                        Patch<String> patch = DiffUtils.diff(lastInvariantFileLines, currentInvariantFileLines);

                        if (patch.getDeltas().size() == 0) {
                            Logger.info("Invariant file " + invariantFile.getName() + " is fixed.");
                            fixedFiles++;
                        }
                    }
                }

                if (fixedFiles == invariantFiles.length) {
                    Logger.info("All invariant files are fixed.");
                    Logger.info("Reached fixed point. Terminating datagen.");
                    System.out.println(); // Makes segments readable.

                    // Dump the invariants we found in this iteration.
                    for (File invariantFile : invariantFiles) {
                        Logger.info("Invariants generated at the end of the " + (iteration - 1) + "th iteration:");
                        Logger.info("----------------");
                        Logger.info("For file " + invariantFile.getName());

                        // Read lines from the file, and insert newlines after each line.
                        // Without using FileOps.
                        StringBuilder sb = new StringBuilder();
                        for (String line : FileOps.readFileLines(invariantFile)) {
                            sb.append(line);
                            sb.append("\n");
                        }
                        System.out.println(sb.toString());
                    }
                    System.exit(0);
                    break;
                }
            }
        } while (!fixedPointReached());
    }

    private static String[] getDatagenClassPath() {
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);
        return classpathEntries;
    }

    private static boolean fixedPointReached() {
        // Dummy implementation for now.
        // Always returns false.
        return false;
    }

    private static Optional<String> getJarFromClassPath(String jarName) {
        // Checks if junit is present in the classpath. If present, returns the path to
        // the jar.
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);

        for (String classpathEntry : classpathEntries) {
            if (classpathEntry.contains(jarName)) {
                String classPathAbsolute = new File(classpathEntry).getAbsolutePath();
                return Optional.of(classPathAbsolute);
            }
        }

        return Optional.empty();
    }

    private static Optional<String> evosuitePresentInClassPath() {
        // Checks if evosuite is present in the classpath.
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);

        for (String classpathEntry : classpathEntries) {
            if (classpathEntry.contains("evosuite")) {
                return Optional.of((new File(classpathEntry)).getAbsolutePath());
            }
        }

        return Optional.empty();
    }

    private static Optional<String> isJunitPresentInClassPath() {
        // Checks if junit is present in the classpath. If present, returns the path to
        // the jar.
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);

        for (String classpathEntry : classpathEntries) {
            if (classpathEntry.contains("junit")) {
                String classPathAbsolute = new File(classpathEntry).getAbsolutePath();
                return Optional.of(classPathAbsolute);
            }
        }

        return Optional.empty();
    }
}
