package edu.boisestate.datagen;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.reporting.Cache;
import edu.boisestate.datagen.rmi.DataPointServerImpl;
import edu.boisestate.datagen.utils.FileOps;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.io.InputStreamReader;
import java.rmi.AlreadyBoundException;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Optional;
import java.util.concurrent.TimeUnit;
import net.sourceforge.argparse4j.ArgumentParsers;
import net.sourceforge.argparse4j.inf.ArgumentParser;
import net.sourceforge.argparse4j.inf.ArgumentParserException;
import net.sourceforge.argparse4j.inf.Namespace;

import org.tinylog.Logger;

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

    private static final int DIG_TIMEOUT = 1500;

    public static void main(String[] args) {
        // Arguments:
        // 1. The path to the source code file(s), This is a folder.
        // 2. Workdir. This is a folder where datagen works.
        // - A {{workdir}}/instrumented/augmented contains the instrumented code with
        // augmentations.
        // - A {{workdir}}/instrumented/reporting contains the code that will report the
        // data to our lib.
        // - A {{workdir}}/compiled/ contains the compiled instrumented code.

        ArgumentParser argParser = ArgumentParsers.newFor("datagen")
                .build()
                .description(
                        "DataGen is a tool for generating data-driven tests for Java programs.");

        argParser
                .addArgument("-s", "--source")
                .help("The path to the source code file(s), This is a folder.")
                .required(true)
                .type(String.class);

        argParser
                .addArgument("-w", "--workdir")
                .help("Working directory for datagen.")
                .required(true)
                .type(String.class);

        argParser
                .addArgument("-e", "--evosuite")
                .help("Evosuite jar file.")
                .required(false)
                .type(String.class);

        argParser
                .addArgument("-j", "--junit")
                .help(
                        "JUnit jar file path. This should also contain the hamcrest jar.")
                .required(false)
                .type(String.class);

        argParser
                .addArgument("-d", "--daikon")
                .help("Daikon jar file path.")
                .required(false)
                .type(String.class);

        argParser
                .addArgument("-k", "--skip_augmentation")
                .help(
                        "Skip augmentation. This means we will run the tests on code without augmenting the branches.")
                .required(false)
                .setDefault(false)
                .type(Boolean.class);

        argParser.addArgument("-m", "--max_iterations")
                .help("Max iteration count for a key")
                .required(false).setDefault(25).type(Integer.class);

        boolean skipAugmentation = false;
        int maxIterationCount = 0;

        // Parse arguments.
        try {
            Namespace ns = argParser.parseArgs(args);
            source = ns.getString("source");
            workdir = ns.getString("workdir");
            evosuiteJarPath = getJarFromClassPath("evosuite").orElse(
                    ns.getString("evosuite"));
            junitJarPath = getJarFromClassPath("junit").orElse(
                    ns.getString("junit"));
            daikonJarPath = getJarFromClassPath("daikon").orElse(
                    ns.getString("daikon"));
            skipAugmentation = ns.getBoolean("skip_augmentation");
            maxIterationCount = ns.getInt("max_iterations");
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
            System.err.println(
                    "Could not start datapointserverimpl - RemoteException.");
            e.printStackTrace();
        }

        // Check classpaths for evosuite and junit.
        if (evosuiteJarPath == null ||
                junitJarPath == null ||
                daikonJarPath == null) {
            System.err.println(
                    "Evosuite, JUnit, or Daikon jar file not provided, and evosuite, junit, or daikon is not present in the classpath.");
            // Print out the status of the jars.
            if (!(evosuiteJarPath == null))
                System.err.println(
                        "Evosuite jar: " + evosuiteJarPath);
            if (!(junitJarPath == null))
                System.err.println(
                        "JUnit jar: " + junitJarPath);
            if (!(daikonJarPath == null))
                System.err.println(
                        "Daikon jar: " + daikonJarPath);
            System.err.println(
                    "Use the -e, -j, and -d flags to provide the evosuite, junit, and daikon jar paths respectively.");
            System.exit(1);
        }

        // Ensure the source path is a directory, and it exists.
        File sourceDir = new File(source);
        if (!sourceDir.exists() || !sourceDir.isDirectory()) {
            Logger.error(
                    "Source path " +
                            sourceDir.getAbsolutePath() +
                            " does not exist or is not a directory.");
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

        int iterations = 0;
        CommentChangingInstrumenter augmenter = new CommentChangingInstrumenter(
                InstrumentationMode.AUGMENTATION,
                skipAugmentation);
        CommentChangingInstrumenter reporter = new CommentChangingInstrumenter(
                InstrumentationMode.INSTRUMENTATION,
                skipAugmentation);
        ImportInstrumenter importer = new ImportInstrumenter();

        // Keys that have stabilized across checks.
        HashMap<String, Integer> stableKeys = new HashMap<>();
        // Cap the max iteration count for all keys.
        HashMap<String, Integer> iterationCounts = new HashMap<>();
        boolean stop = false;
        Checkpoint checkpoint = new Checkpoint(3);

        // Main loop.
        do {
            // Reset targeted information.
            long startTime = System.currentTimeMillis();

            System.out.println();
            Logger.info(
                    "---------------------- Starting iteration " +
                            ++iterations +
                            "--------------------");
            // Make a checkpoint directory.
            File checkpointDir = new File(checkpointPath + "/" + iterations);
            FileOps.createDirectory(checkpointDir.getAbsolutePath());

            File codePath = new File(checkpointDir.getAbsolutePath() + "/code");
            FileOps.createDirectory(codePath.getAbsolutePath());

            // Clear out the augmented and reporting directories.
            FileOps.recursivelyDeleteFolder(new File(augmentedPath));
            FileOps.recursivelyDeleteFolder(new File(reportingPath));

            // Copy the original source to instrumentation directories.
            FileOps.recursivelyCopyFolder(sourceDir, new File(augmentedPath));
            FileOps.recursivelyCopyFolder(sourceDir, new File(reportingPath));

            // Code in the reporting directory is instrumented with reporting code.
            HashSet<String> instrumentationPoints = new HashSet<>();
            for (File file : new File(reportingPath).listFiles()) {
                if (file.getName().endsWith(".java")) {
                    Logger.info("Instrumenting file: " + file.getName());
                    CompilationUnit cu = parseJavaFile(file).orElseThrow();
                    reporter.instrument(cu);
                    importer.instrument(cu);

                    instrumentationPoints = reporter.getInstrumentationPoints();

                    FileOps.writeFile(file, cu.toString());
                }
            }

            Cache.getInstance().resetTargetedInformation(instrumentationPoints);

            // Code in the augmented directory is augmented with data we have seen
            // in new NewCache. Then, it is compiled and executed on evosuite.
            for (File file : new File(augmentedPath).listFiles()) {
                if (!file.getName().endsWith(".java")) {
                    // Skip all non-java files.
                    continue;
                }
                String className = file.getName().replace(".java", "");

                if (file.getName().endsWith(".java")) {
                    CompilationUnit cu = parseJavaFile(file).orElseThrow();
                    augmenter.instrument(cu);
                    FileOps.writeFile(file, cu.toString());
                }

                Logger.info("Compiling augmented file " + file.getName());
                // Compile and execute the augmented file.
                String[] command = {
                        "javac",
                        file.getAbsolutePath(),
                        "-d",
                        compiledPath,
                };
                runProcess(command);

                Logger.info(
                        "Running evosuite on augmented file " + file.getName());
                // Run evosuite on the file, but from the compiled directory.
                String compiledFilePath = compiledPath;
                String[] evoruncommand = {
                        "java",
                        "-cp",
                        String.join(":", classpaths),
                        "-jar",
                        evosuiteJarPath,
                        String.format("-projectCP=%s", compiledFilePath),
                        String.format("-class=%s", className),
                        String.format("-Dassertions=false"),
                        "-Dcriterion=BRANCH",
                        "-Dalgorithm=MOSA",
                        "-Dprimitive_pool=0.0",
                        "-Dprimitive_reuse_probability=0.05" // Very low prob. of reusing constants in case required.
                };

                runProcess(evoruncommand);
            }
            long endEvoTime = System.currentTimeMillis();
            Logger.debug(
                    "Evosuite run took " + (endEvoTime - startTime) + " ms.");

            // Now that evosuite run has finished, our tests are generated in
            // $PWD/evosuite-tests. They need to be compiled alongside our reporting
            // code, and run together.
            for (File file : new File(reportingPath).listFiles()) {
                if (!file.getName().endsWith(".java")) {
                    // Skip all non-java files.
                    continue;
                }

                Logger.info("Compiling reporting file " + file.getName());
                String className = file.getName().replace(".java", "");
                String[] compile_reportingfiles = {
                        "javac",
                        "-cp",
                        String.join(":", classpaths),
                        file.getAbsolutePath(),
                        "-d",
                        compiledPath,
                };
                runProcess(compile_reportingfiles);

                // Also compile the respective evosuite test. The two files
                // we need to compile in this case are:
                // className_ESTest.java
                // className_ESTest_scaffolding.java

                Logger.info(
                        "Compiling evosuite test file for " + file.getName());
                // Now compile all files in evosuite-tests folder.
                File evosuiteTestFileName = new File(
                        evosuiteTests.getAbsolutePath() +
                                "/" +
                                className +
                                "_ESTest.java");
                File scaffoldingFileName = new File(
                        evosuiteTests.getAbsolutePath() +
                                "/" +
                                className +
                                "_ESTest_scaffolding.java");

                String[] compile_esfiles = {
                        "javac",
                        "-d",
                        compiledPath,
                        "-cp",
                        String.join(":", classpaths),
                        evosuiteTestFileName.getAbsolutePath(),
                };

                runProcess(compile_esfiles);

                String[] compile_scaffolding = {
                        "javac",
                        "-d",
                        compiledPath,
                        "-cp",
                        String.join(":", classpaths),
                        scaffoldingFileName.getAbsolutePath(),
                };
                runProcess(compile_scaffolding);

                Logger.info(
                        "Running JUnit tests generated for " + file.getName());
                // Run the compiled junit tests on junit.
                String[] junitcommand = {
                        "java",
                        "-cp",
                        String.join(":", classpaths),
                        "org.junit.runner.JUnitCore",
                        className + "_ESTest",
                };
                runProcess(junitcommand);
            }

            // Dump all "targeted" information - i.e. all code paths that were actually
            // visited.
            Logger.info(
                    "The following instrumentation points were hit in this run:");
            Logger.info(
                    String.join(
                            ", ",
                            Cache.getInstance().getAllTargetsVisited().toString()));

            // Now that everything is done, we will dump the data to the "code" directory,
            // Alongside generated evosuite tests, augmented code, and reporting code.
            FileOps.recursivelyCopyFolder(
                    new File(reportingPath),
                    new File(checkpointDir.getAbsolutePath() + "/reporting"));
            FileOps.recursivelyCopyFolder(
                    new File(augmentedPath),
                    new File(checkpointDir.getAbsolutePath() + "/augmented"));
            FileOps.recursivelyCopyFolder(
                    evosuiteTests,
                    new File(checkpointDir.getAbsolutePath() + "/evosuite-tests"));

            // Generate our code.
            Logger.info("Generating code for Daikon and DIG.");
            Cache.getInstance().writeTracesTo(codePath);

            // Now run DIG/Daikon on the files.
            for (String instrumentationPoint : instrumentationPoints) {
                if (stableKeys.containsKey(instrumentationPoint)) {
                    Logger.debug("Skipping generation for stable key " + instrumentationPoint);
                    continue;
                }

                iterationCounts.put(instrumentationPoint,
                        iterationCounts.getOrDefault(instrumentationPoint, maxIterationCount) - 1);
                if (iterationCounts.get(instrumentationPoint) == 0) {
                    Logger.warn("Key " + instrumentationPoint + " did not stabilize within 100 iterations.");
                    stableKeys.put(instrumentationPoint, iterations);
                }

                Logger.debug(String.format("Working on unstable key: %s (%d)", instrumentationPoint,
                        checkpoint.getConsideredIterationDaikon(instrumentationPoint) - iterations));

                // Run Dig and Daikon on the path.
                runDaikonOnDtraceFile(
                        new File(String.format("%s/%s.dtrace", codePath.getAbsolutePath(), instrumentationPoint)),
                        classpaths,
                        new File(
                                String.format("%s/%s.daikonoutput", codePath.getAbsolutePath(), instrumentationPoint)));

                runDigOnCSVFile(
                        instrumentationPoint,
                        iterations,
                        checkpoint,
                        new File(String.format("%s/%s.csv", codePath.getAbsolutePath(),
                                instrumentationPoint)),
                        new File(String.format("%s/%s.digoutput", codePath.getAbsolutePath(),
                                instrumentationPoint)));
            }

            // For each Daikon and DIG file, check if it has changed from the last iteration
            // using our checkpoint.
            int totalChangedInvariants = 0;
            for (String key : instrumentationPoints) {
                // No need to compare stable keys.
                if (stableKeys.containsKey(key))
                    continue;

                String thisIterationDaikonFileContents = FileOps
                        .readFile(new File(String.format("%s/%s.daikonoutput", codePath.getAbsolutePath(), key)));

                String thisIterationDigFileContents = FileOps
                        .readFile(new File(String.format("%s/%s.digoutput", codePath.getAbsolutePath(), key)));

                // We perform the preliminary check on Daikon only, because DIG is
                // expensive to compute. In either case, BOTH Daikon and DIG must stabilize for
                // a program
                // point.
                if (checkpoint.hasChangedDaikon(key, iterations, thisIterationDaikonFileContents)) {
                    totalChangedInvariants += 1;
                } else {
                    if (checkpoint.hasChangedDig(key, iterations, thisIterationDigFileContents)) {
                        totalChangedInvariants += 1;
                    } else {
                        stableKeys.put(key, iterations);
                    }
                }
            }

            stop = totalChangedInvariants == 0;

            long endTime = System.currentTimeMillis();
            Logger.debug(
                    "Iteration " +
                            iterations +
                            " took " +
                            (endTime - startTime) +
                            " ms.");

            if (stop) {
                Logger.info("Running the final invariant generation for all instrumentation points");
                for (String key : instrumentationPoints) {
                    // Put all generated invariants directly in the workdir, like
                    // "checkpoint_datagen/a_lt_b_truebranch.daikonoutput". Makes it
                    // easier to see what the final invariants were.
                    runDaikonOnDtraceFile(
                            new File(
                                    String.format(
                                            "%s/%s.dtrace",
                                            codePath.getAbsolutePath(),
                                            key)),
                            classpaths,
                            new File(String.format("%s/%s.daikonoutput", workdir, key)));

                    runDigOnCSVFile(key,
                            iterations,
                            checkpoint,
                            new File(
                                    String.format(
                                            "%s/%s.csv",
                                            codePath.getAbsolutePath(),
                                            key)),
                            new File(
                                    String.format(
                                            "%s/%s.digoutput",
                                            workdir,
                                            key)));
                }
            }
        } while (!stop);

        System.out.println(
                "----------------------------------------------------------");
        System.out.println(
                "The following iterations caused each key's stabilization:");
        for (String key : stableKeys.keySet()) {
            System.out.println(
                    String.format(
                            "Key: %s, iteration: %d",
                            key,
                            stableKeys.get(key)));
        }

        // Required to shutdown the RMI server, etc. TODO: Find a better way to do this
        // later.
        System.exit(0);
    }

    private static void runDaikonOnDtraceFile(
            File DTraceFile,
            String[] classpaths,
            File outputFile) {
        // Run daikon on the dtrace file.
        String[] daikonCommand = {
                "java",
                "-cp",
                String.join(":", classpaths),
                "daikon.Daikon",
                DTraceFile.getAbsolutePath(),
                // codePath + "/" + key + ".dtrace",
        };

        String daikonOutput = runProcess(daikonCommand);
        // Store the file in the code path with daikonoutput extension.
        FileOps.writeFile(outputFile, daikonOutput);
    }

    private static void runDigOnCSVFile(String instrumentationPoint, Integer iteration, Checkpoint cp, File CSVFile,
            File outputFile) {
        // Run Dig on the trace csv file.
        String[] digCommand = {
                "python3",
                "-O",
                "../../../../dig/src/dig.py",
                "--seed",
                "12345", // Help for debugging later.
                CSVFile.getAbsolutePath(),
        };

        // DIG cannot be run with the runProcess command, because it times out sometimes
        // so we need a custom implementation.
        ProcessBuilder pb = new ProcessBuilder(digCommand);
        Process process = null;
        try {
            StringBuilder sb = new StringBuilder();

            // Set pb to cwd.
            pb.directory(new File(System.getProperty("user.dir")));
            pb.redirectErrorStream(true);

            process = pb.start();
            // Add the timeout here
            boolean completed = process.waitFor(DIG_TIMEOUT, TimeUnit.SECONDS);

            if (!completed) {
                // Process didn't complete within the timeout period
                throw new InterruptedException("Process timed out");
            }

            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(process.getInputStream()));

            String lineStdout;
            while ((lineStdout = reader.readLine()) != null) {
                sb.append(lineStdout);
                sb.append("\n");
            }

            String digOutput = sb.toString();

            /*
             * Here is the issue with this - unlike Daikon, dig prints out the file names
             * in the output, and also prints the minimization count, trace count, etc. So
             * the output of DIG will ALWAYS change between iterations, and fixed point will
             * never be reached in the output string. So we strip all metadata from dig
             * output,
             * and just store the line starting at vtrace ({count} invs):, and following
             * invariants.
             */

            sb = new StringBuilder(); // Discard old string.

            String[] digOutputLines = digOutput.split(System.lineSeparator());
            boolean vtraceLineFound = false;
            for (String line : digOutputLines) {
                if (line.startsWith("vtrace"))
                    vtraceLineFound = true;
                if (vtraceLineFound) {
                    sb.append(line);
                    sb.append("\n");
                }
            }
            String toSaveString = sb.toString();

            // Store the dig invariants generated with digoutput extension.
            FileOps.writeFile(outputFile, toSaveString);

        } catch (InterruptedException e) {
            process.destroyForcibly();
            Logger.warn("DIG did not complete in time for " + CSVFile.getName()
                    + "; " + instrumentationPoint + " will be reset to current iteration " + iteration);

            String oldFilePath = String.format("%s/checkpoint/%d/%s.digoutput", (new File(workdir)).getAbsolutePath(),
                    iteration - 1,
                    instrumentationPoint);

            // Copy over the file from the last iteration to this one.
            FileOps.copyFile(
                    new File(oldFilePath),
                    outputFile);

            cp.deleteDigInfo(instrumentationPoint);
            return;

        } catch (IOException e) {
            // IOException means we couldn't run the process. Fatal crash.
            e.printStackTrace();
            System.err.println(">> There was an error running the DIG tool <<");
            System.exit(-1);
        }
    }

    // Run a process and return the stdout+stderr of that process.
    private static String runProcess(String[] command) {
        StringBuilder sb = new StringBuilder();
        try {
            ProcessBuilder pb = new ProcessBuilder(command);
            // Set pb to cwd.
            pb.directory(new File(System.getProperty("user.dir")));
            pb.redirectErrorStream(true);
            Process p = pb.start();
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(p.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                sb.append(line);
                sb.append("\n");
            }

            p.waitFor();
            if (!(p.exitValue() == 0)) {
                System.err.println("Error running command: ");
                System.err.println(sb.toString());
                System.exit(1);
            }

            return sb.toString();
        } catch (Exception e) {
            e.printStackTrace();
            System.err.println(e);
            System.exit(1);
        }

        // This should be an unreachable path.
        throw new IllegalArgumentException("Should not be reachable.");
    }

    private static Optional<CompilationUnit> parseJavaFile(File file) {
        JavaParser parser = new JavaParser();
        try {
            CompilationUnit cu = parser.parse(file).getResult().get();
            return Optional.of(cu);
        } catch (Exception e) {
            return Optional.empty();
        }
    }

    private static String[] getDatagenClassPath() {
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);
        return classpathEntries;
    }

    private static Optional<String> getJarFromClassPath(String jarName) {
        // Checks if junit is present in the classpath. If present, returns the path to
        // the jar.
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);

        for (String classpathEntry : classpathEntries) {
            if (classpathEntry.contains(jarName)) {
                String classPathAbsolute = new File(
                        classpathEntry).getAbsolutePath();
                return Optional.of(classPathAbsolute);
            }
        }

        return Optional.empty();
    }
}
