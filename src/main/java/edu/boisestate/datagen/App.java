package edu.boisestate.datagen;

import java.io.File;
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

import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.rmi.DataPointServerImpl;
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
    private static String codefolder;
    private static String evosuiteJarPath;
    private static String junitJarPath;
    private static String daikonJarPath;

    private static int iteration;
    private static int numIterations = -1;

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

        // TODO: This is not working ATM.
        argParser.addArgument("-i", "--iterations")
                .help("Number of iterations to run (overrides the fixed point check in daikon).")
                .required(false)
                .type(Integer.class);

        // Parse arguments.
        try {
            Namespace ns = argParser.parseArgs(args);
            source = ns.getString("source");
            workdir = ns.getString("workdir");
            evosuiteJarPath = getJarFromClassPath("evosuite").orElse(ns.getString("evosuite"));
            junitJarPath = getJarFromClassPath("junit").orElse(ns.getString("junit"));
            daikonJarPath = getJarFromClassPath("daikon").orElse(ns.getString("daikon"));
            numIterations = ns.getInt("iterations");

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

        int iterations = 0;
        CommentChangingInstrumenter augmenter = new CommentChangingInstrumenter(
                InstrumentationMode.AUGMENTATION);
        CommentChangingInstrumenter reporter = new CommentChangingInstrumenter(
                InstrumentationMode.INSTRUMENTATION);
        ImportInstrumenter importer = new ImportInstrumenter();

        // Main loop.
        do {
            Logger.info("---------------------- Starting iteration " + iterations);

            // Clear out the augmented and reporting directories.
            FileOps.recursivelyDeleteFolder(new File(augmentedPath));
            FileOps.recursivelyDeleteFolder(new File(reportingPath));

            // Copy the original source to instrumentation directories.
            FileOps.recursivelyCopyFolder(sourceDir, new File(augmentedPath));
            FileOps.recursivelyCopyFolder(sourceDir, new File(reportingPath));

            // Code in the augmented directory is augmented with data we have seen
            // in new NewCache.
            for (File file : new File(augmentedPath).listFiles()) {
                if (file.getName().endsWith(".java")) {
                    Logger.info("Augmenting file: " + file.getName());
                    CompilationUnit cu = parseJavaFile(file).orElseThrow();
                    augmenter.instrument(cu);
                    FileOps.writeFile(file, cu.toString());
                }
            }

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

            System.exit(0);

        } while (!fixedPointReached());
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

    private static boolean fixedPointReached() {
        if (numIterations != -1 && iteration == numIterations)
            return true;
        else {
            if (iteration == 1)
                return false;
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
                    return false;
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
                    return true;
                }
            }
        }
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
}
