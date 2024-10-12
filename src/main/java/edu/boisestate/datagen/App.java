package edu.boisestate.datagen;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import edu.boisestate.datagen.exprcompiler.CompiledExpression;
import edu.boisestate.datagen.exprcompiler.InvCompiler;
import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.reporting.Cache;
import edu.boisestate.datagen.rmi.DataPointServerImpl;
import edu.boisestate.datagen.utils.FileOps;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.rmi.AlreadyBoundException;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Optional;
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
                "DataGen is a tool for generating data-driven tests for Java programs."
            );

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
                "JUnit jar file path. This should also contain the hamcrest jar."
            )
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
                "Skip augmentation. This means we will run the tests on code without augmenting the branches."
            )
            .required(false)
            .setDefault(false)
            .type(Boolean.class);

        boolean skipAugmentation = false;

        // Parse arguments.
        try {
            Namespace ns = argParser.parseArgs(args);
            source = ns.getString("source");
            workdir = ns.getString("workdir");
            evosuiteJarPath = getJarFromClassPath("evosuite").orElse(
                ns.getString("evosuite")
            );
            junitJarPath = getJarFromClassPath("junit").orElse(
                ns.getString("junit")
            );
            daikonJarPath = getJarFromClassPath("daikon").orElse(
                ns.getString("daikon")
            );
            skipAugmentation = ns.getBoolean("skip_augmentation");
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
                "Could not start datapointserverimpl - RemoteException."
            );
            e.printStackTrace();
        }

        // Check classpaths for evosuite and junit.
        if (
            evosuiteJarPath == null ||
            junitJarPath == null ||
            daikonJarPath == null
        ) {
            System.err.println(
                "Evosuite, JUnit, or Daikon jar file not provided, and evosuite, junit, or daikon is not present in the classpath."
            );
            // Print out the status of the jars.
            if (!(evosuiteJarPath == null)) System.err.println(
                "Evosuite jar: " + evosuiteJarPath
            );
            if (!(junitJarPath == null)) System.err.println(
                "JUnit jar: " + junitJarPath
            );
            if (!(daikonJarPath == null)) System.err.println(
                "Daikon jar: " + daikonJarPath
            );
            System.err.println(
                "Use the -e, -j, and -d flags to provide the evosuite, junit, and daikon jar paths respectively."
            );
            System.exit(1);
        }

        // Ensure the source path is a directory, and it exists.
        File sourceDir = new File(source);
        if (!sourceDir.exists() || !sourceDir.isDirectory()) {
            Logger.error(
                "Source path " +
                sourceDir.getAbsolutePath() +
                " does not exist or is not a directory."
            );
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
            skipAugmentation
        );
        CommentChangingInstrumenter reporter = new CommentChangingInstrumenter(
            InstrumentationMode.INSTRUMENTATION,
            skipAugmentation
        );
        ImportInstrumenter importer = new ImportInstrumenter();

        /*
         * We do not check a instrumentation key, once it has stabilized between two
         * runs, because there's always a probability in later future, where a new data
         * point can cause it to change. So the threshold for now is 2 consecutive
         * iterations.
         * If between two iterations the invariants generated for a ppt do not change
         * for both
         * dig and daikon, then we consider that ppt invariant generated to be stable.
         */
        HashMap<String, Integer> stableKeys = new HashMap<>();

        // Main loop.
        do {
            // Reset targeted information.
            Cache.getInstance().resetTargetedInformation();

            long startTime = System.currentTimeMillis();
            System.out.println();
            Logger.info(
                "---------------------- Starting iteration " +
                ++iterations +
                "--------------------"
            );
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
            for (File file : new File(reportingPath).listFiles()) {
                if (file.getName().endsWith(".java")) {
                    Logger.info("Instrumenting file: " + file.getName());
                    CompilationUnit cu = parseJavaFile(file).orElseThrow();
                    reporter.instrument(cu);
                    importer.instrument(cu);
                    FileOps.writeFile(file, cu.toString());
                }
            }

            // Code in the augmented directory is augmented with data we have seen
            // in new NewCache. Then, it is compiled and executed on evosuite.
            for (File file : new File(augmentedPath).listFiles()) {
                if (!file.getName().endsWith(".java")) {
                    // Skip all non-java files.
                    continue;
                }
                String className = file.getName().replace(".java", "");

                Logger.info("Augmenting input file " + file.getName());
                if (file.getName().endsWith(".java")) {
                    Logger.info("Augmenting file: " + file.getName());
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
                    "Running evosuite on augmented file " + file.getName()
                );
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
                };

                runProcess(evoruncommand);
            }
            long endEvoTime = System.currentTimeMillis();
            Logger.debug(
                "Evosuite run took " + (endEvoTime - startTime) + " ms."
            );

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
                    "Compiling evosuite test file for " + file.getName()
                );
                // Now compile all files in evosuite-tests folder.
                File evosuiteTestFileName = new File(
                    evosuiteTests.getAbsolutePath() +
                    "/" +
                    className +
                    "_ESTest.java"
                );
                File scaffoldingFileName = new File(
                    evosuiteTests.getAbsolutePath() +
                    "/" +
                    className +
                    "_ESTest_scaffolding.java"
                );

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
                    "Running JUnit tests generated for " + file.getName()
                );
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
                "The following instrumentation points were hit in this run:"
            );
            Logger.info(
                String.join(
                    ", ",
                    Cache.getInstance().getAllTargetsVisited().toString()
                )
            );

            // Now that everything is done, we will dump the data to the "code" directory,
            // Alongside generated evosuite tests, augmented code, and reporting code.
            FileOps.recursivelyCopyFolder(
                new File(reportingPath),
                new File(checkpointDir.getAbsolutePath() + "/reporting")
            );
            FileOps.recursivelyCopyFolder(
                new File(augmentedPath),
                new File(checkpointDir.getAbsolutePath() + "/augmented")
            );
            FileOps.recursivelyCopyFolder(
                evosuiteTests,
                new File(checkpointDir.getAbsolutePath() + "/evosuite-tests")
            );

            // Generate our code.
            Logger.info("Generating code.");
            HashMap<String, String> traces = Cache.getInstance()
                .generate_daikon_dtraces();

            for (String key : traces.keySet()) {
                FileOps.writeFile(
                    new File(codePath + "/" + key + ".dtrace"),
                    traces.get(key)
                );

                if (stableKeys.containsKey(key)) {
                    Logger.debug(
                        "Skipping key " +
                        key +
                        " for Daikon but the DTrace file is written."
                    );
                    continue;
                }

                if (!Cache.getInstance().wasTargeted(key)) {
                    Logger.debug(
                        "Skipping key " +
                        key +
                        " even though it's not stable, because it was not visited."
                    );
                }

                runDaikonOnDtraceFile(
                    new File(codePath + "/" + key + ".dtrace"),
                    classpaths,
                    new File(codePath + "/" + key + ".daikonoutput")
                );
            }

            Logger.info("Finished executing daikon and generating invariants.");

            HashMap<String, String> dig_traces = Cache.getInstance()
                .generate_dig_traces();

            for (String key : dig_traces.keySet()) {
                Logger.debug("Dig working with key " + key);
                FileOps.writeFile(
                    new File(codePath + "/" + key + ".csv"),
                    dig_traces.get(key)
                );

                if (stableKeys.containsKey(key)) {
                    Logger.debug(
                        "Skipping key " +
                        key +
                        " for DIG but the CSV file is written."
                    );
                    continue;
                }

                if (!Cache.getInstance().wasTargeted(key)) {
                    Logger.debug(
                        "Skipping key " +
                        key +
                        " even though it's not stable, because it was not visited."
                    );
                }

                runDigOnCSVFile(
                    new File(
                        String.format(
                            "%s/%s.csv",
                            codePath.getAbsolutePath(),
                            key
                        )
                    ),
                    new File(codePath + "/" + key + ".digoutput")
                );
            }

            // Check if all of the files have stabilized. For this, we need to recursively
            // descend into the
            // checkpoint folder, list all files from previous iteration inside the 'code'
            // folder, and check
            // if the file content has changed.
            if (iterations == 1) {
                Logger.info(
                    "Finished first iteration. No stabilization checks will be done"
                );
            } else {
                Logger.debug(
                    "Checking if all invariants have become stable or not."
                );

                // Get all keys from cache we can compare.
                List<String> cacheKeys = Cache.getInstance()
                    .getInstrumentationCacheKeys();
                int changedInvariantsCount = 0;

                for (String key : cacheKeys) {
                    if (stableKeys.containsKey(key)) {
                        // We do not care what dig produced at this point, we will skip it.
                        continue;
                    }

                    if (!Cache.getInstance().wasTargeted(key)) {
                        Logger.debug(
                            "Since " +
                            key +
                            " was not visited, we will try to target it again."
                        );
                        Logger.debug(
                            key + " will be considered to have been changed"
                        );

                        // let's consider this to have changed for both DIG and Daikon.
                        changedInvariantsCount += 2;
                        continue;
                    }

                    Logger.debug("Checking if " + key + " has changed");
                    if (
                        Checkpoint.getInstance()
                            .checkChangeInWindow(
                                checkpointPath,
                                key,
                                iterations
                            )
                    ) {
                        changedInvariantsCount += 1;
                    }
                }

                if (changedInvariantsCount == 0) {
                    Logger.info(
                        "All invariants have stabilized at iteration " +
                        iterations
                    );

                    Logger.info(
                        "Running final invariant generation for each point"
                    );
                    for (String key : stableKeys.keySet()) {
                        Logger.debug("Running Daikon for key " + key);
                        runDaikonOnDtraceFile(
                            new File(codePath + "/" + key + ".dtrace"),
                            classpaths,
                            new File(codePath + "/" + key + ".daikonoutput")
                        );

                        Logger.debug("Running DIG for key " + key);
                        runDigOnCSVFile(
                            new File(
                                String.format(
                                    "%s/%s.csv",
                                    codePath.getAbsolutePath(),
                                    key
                                )
                            ),
                            new File(codePath + "/" + key + ".digoutput")
                        );
                    }

                    System.out.println(
                        "----------------------------------------------------------"
                    );
                    System.out.println(
                        "The following iterations caused each key's stabilization:"
                    );
                    for (String key : stableKeys.keySet()) {
                        System.out.println(
                            String.format(
                                "Key: %s, iteration: %d",
                                key,
                                stableKeys.get(key)
                            )
                        );
                    }
                    System.out.println(
                        "----------------------------------------------------------"
                    );
                    Logger.info("Processed " + iterations + " iterations.");
                    System.exit(0);
                }
            }

            long endTime = System.currentTimeMillis();
            Logger.debug(
                "Iteration " +
                iterations +
                " took " +
                (endTime - startTime) +
                " ms."
            );
        } while (true);
    }

    private static void runDaikonOnDtraceFile(
        File DTraceFile,
        String[] classpaths,
        File outputFile
    ) {
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

    private static void runDigOnCSVFile(File CSVFile, File outputFile) {
        // Run Dig on the trace csv file.
        String[] digCommand = {
            "python3",
            "-O",
            "../../../../dig/src/dig.py",
            "--seed",
            "12345", // Help for debugging later.
            CSVFile.getAbsolutePath(),
        };

        /*
         * Here is the issue with this - unlike Daikon, dig prints out the file names
         * in the output, and also prints the minimization count, trace count, etc. So
         * the output of DIG will ALWAYS change between iterations, and fixed point will
         * never be reached in the output string. So we strip all metadata from dig
         * output,
         * and just store the line starting at vtrace ({count} invs):, and following
         * invariants.
         */

        String digOutput = runProcess(digCommand);
        StringBuilder sb = new StringBuilder();
        String[] digOutputLines = digOutput.split(System.lineSeparator());
        boolean vtraceLineFound = false;
        for (String line : digOutputLines) {
            if (line.startsWith("vtrace")) vtraceLineFound = true;
            if (vtraceLineFound) {
                sb.append(line);
                sb.append("\n");
            }
        }
        String toSaveString = sb.toString();

        // Store the dig invariants generated with digoutput extension.
        FileOps.writeFile(outputFile, toSaveString);
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
                new InputStreamReader(p.getInputStream())
            );
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
                    classpathEntry
                ).getAbsolutePath();
                return Optional.of(classPathAbsolute);
            }
        }

        return Optional.empty();
    }
}
