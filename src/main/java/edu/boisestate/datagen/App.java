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
import java.util.Optional;

import org.tinylog.Logger;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.codegen.Codegen;
import edu.boisestate.datagen.instrumenters.IfStatementInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.instrumenters.TestCaseInstrumenter;
import edu.boisestate.datagen.instrumenters.Wrapper;
import edu.boisestate.datagen.rmi.DataPointServerImpl;
import edu.boisestate.datagen.utils.Compiler;
import edu.boisestate.datagen.utils.FileOps;
import net.sourceforge.argparse4j.*;
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
            System.err.println("Evosuite, JUnit, or Daikon jar file not provided, and evosuite, junit, or daikon is not present in the classpath.");
            // Print out the status of the jars.
            if (!(evosuiteJarPath == null))
            System.err.println("Evosuite jar: " + evosuiteJarPath);
            if (!(junitJarPath == null))
            System.err.println("JUnit jar: " + junitJarPath);
            if (!(daikonJarPath == null))
            System.err.println("Daikon jar: " + daikonJarPath);
            System.err.println("Use the -e, -j, and -d flags to provide the evosuite, junit, and daikon jar paths respectively.");
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
                System.err.println("Augmenting " + augmentedFile.getName()); 
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

            Logger.info("---------------- Iteration " + iteration++ + " ----------------");
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

            // Run evosuite on each compiled file.
            for (File javaFile : javaFilesCompiled) {
                File file = new File(javaFile.getAbsolutePath());
                System.out.println("File: " + file.getName());

                String className = file.getName().substring(0, file.getName().length() - 6);
                System.out.println("Class name: " + className);

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

                    Logger.info("Evosuite finished running on " + className);
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
                System.out.println("Finished running evosuite.");
            }

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
                    System.out.println("# Running JUnit tests from " + evosuiteTestFile.getName());
                    Process p = pb.start();
                    // print the output of the process
                    BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
                    String line;
                    StringBuilder sb = new StringBuilder();
                    while ((line = reader.readLine()) != null) {
                        sb.append(line);
                    }
                    p.waitFor();
                    System.out.println("# JUnit finished running on " + evosuiteTestFile.getName());
                    // Check the exit code of the process.
                    // if (p.exitValue() != 0) {
                    //     System.err.println("JUnit exited with non-zero exit code. Exit code: " + p.exitValue());
                    //     System.err.println("JUnit output:");
                    //     System.err.println(sb.toString());
                    //     System.exit(1);
                    // }
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

            // Compile the stuff in the checkpoint/code folder, along with 
            // everything we have in the compiled folder, and run it on daikon to generate the output.
            // Store the daikon output in the same folder as "code", and compare previous iterations
            // to the current one for stability and fixed point.
            // TODO: find numeric metrics to compare strings for equality.

            // Wipe out the augmented, reporting, and compiled folders.
            FileOps.recursivelyDeleteFolder(new File(augmentedPath));
            FileOps.recursivelyDeleteFolder(new File(reportingPath));
            FileOps.recursivelyDeleteFolder(new File(compiledPath));

            long endTime = System.currentTimeMillis();
            long elapsedTime = endTime - startTime;
            Logger.debug("Iteration " + iteration + " took " + elapsedTime + " milliseconds.");
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
