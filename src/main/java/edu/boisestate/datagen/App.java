package edu.boisestate.datagen;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Optional;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.IfStatementInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.instrumenters.TestCaseInstrumenter;
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

        try {
            // Parse the arguments.
            Namespace ns = argParser.parseArgs(args);
            source = ns.getString("source");
            workdir = ns.getString("workdir");

            String evosuiteJarPath = evosuitePresentInClassPath().orElse(ns.getString("evosuite"));
            String junitJarPath = isJunitPresentInClassPath().orElse(ns.getString("junit"));

            if (evosuiteJarPath == null || junitJarPath == null) {
                System.err.println(
                        "Evosuite jar file not provided, and evosuite or junit is not present in the classpath.");
                System.err.println("Use the -e and -j flags to provide the evosuite and junit jar paths.");
                System.exit(1);
            }

            System.out.println("Source path: " + source);
            System.out.println("Workdir path: " + workdir);

            // Ensure the source path is a directory, and it exists.
            File sourceDir = new File(source);
            if (!sourceDir.isDirectory()) {
                System.err.println("Source path is not a directory.");
                System.exit(1);
            }
            if (!sourceDir.exists()) {
                System.err.println("Source path does not exist.");
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

            String[] classpaths = classpathsList.toArray(new String[]{});


            // Find all .java files in the source directory.
            File[] javaFiles = sourceDir.listFiles(file -> file.getName().endsWith(".java"));

            // 1. For each .java file, add relevant imports, and add reporting methods on
            // the
            // branches and loops bodies (instrument paths). Then save them to the
            // "reporting" folder.
            // and also the augmented folder (since at the beginning, both should be the
            // same).
            for (File javaFile : javaFiles) {
                File file = new File(javaFile.getAbsolutePath());
                System.out.println("File: " + file.getName());

                String contents = FileOps.readFile(file);

                // Dump the file to the augmented folder.
                // At the beginning, the augmented folder should be the same as the
                // original folder.
                try {
                    FileWriter fw = new FileWriter(augmentedPath + "/" + javaFile.getName());
                    fw.write(contents);
                    fw.close();

                } catch (IOException e) {
                    e.printStackTrace();
                    System.exit(1);
                }

                // Reporting code is mixed with the original code. This will be later executed
                // alongside compiled tests from evosuite, to report the method that was
                // executed
                // on evosuite side, and the data that the method generated.
                JavaParser parser = new JavaParser();
                CompilationUnit cu = parser.parse(contents).getResult().orElseThrow();

                ImportInstrumenter importInstrumenter = new ImportInstrumenter();
                IfStatementInstrumenter ifInstrumenter = new IfStatementInstrumenter(
                        InstrumentationMode.INSTRUMENTATION,
                        null);

                cu.findAll(CompilationUnit.class).stream().forEach(importInstrumenter::instrument);
                cu.findAll(CompilationUnit.class).stream().forEach(ifInstrumenter::instrument);

                try {
                    FileWriter fw2 = new FileWriter(reportingPath + "/" + javaFile.getName());
                    fw2.write(cu.toString());
                    fw2.close();

                } catch (IOException e) {
                    e.printStackTrace();
                    System.exit(1);
                }
            }

            // In a loop:
            do {
                // Start off by creating a checkpoint folder.
                String checkpointFolder = (checkpointPath + File.separator + iteration);
                FileOps.createDirectory(checkpointFolder);

                // For each .java file in the augmented folder, compile it, and
                // run it on evosuite. After evosuite generates the test cases,
                // instrument the test cases with method invocation instrumentation,
                // compile the reporting code along with the evosuite test cases,
                // and run it along with evosuite.

                File augmentedFiles = new File(augmentedPath);
                File[] javaFilesAugmented = augmentedFiles.listFiles(file -> file.getName().endsWith(".java"));

                for (File javaFile : javaFilesAugmented) {
                    File file = new File(javaFile.getAbsolutePath());

                    // Now here. The files require the classpath to be set to the library,
                    // and the source folder passed as the first argument.
                    Compiler.compile(file.getAbsolutePath(), compiledPath, classpaths);
                }

                // List all compiled files in the compiled folder.
                File compiledFiles = new File(compiledPath);
                File[] javaFilesCompiled = compiledFiles.listFiles(file -> file.getName().endsWith(".class"));

                // Run each compiled file on evosuite.
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
                        System.out.println("# Running evosuite on " + className);
                        Process p = pb.start();
                        // print the output of the process
                        BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
                        String line;
                        StringBuilder sb = new StringBuilder();
                        while ((line = reader.readLine()) != null) {
                            sb.append(line);
                        }
                        p.waitFor();
                        System.out.println("# Evosuite finished running on " + className);
                        // Check the exit code of the process.
                        if (p.exitValue() != 0) {
                            System.err.println("Evosuite exited with non-zero exit code.");
                            System.err.println("Evosuite output:");
                            System.err.println(sb.toString());
                            System.exit(1);
                        }
                    } catch (IOException | InterruptedException e) {
                        e.printStackTrace();
                        System.exit(1);
                    }
                    System.out.println("Finished running evosuite.");
                }

                // Now, instrument the evosuite testcases with method invocation
                // instrumentation.
                // Evosuite tests are generated in the $PWD/evosuite-tests folder.

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
                    JavaParser parser = new JavaParser();
                    CompilationUnit cu = parser.parse(contents).getResult().orElseThrow();
                    if (evosuiteTestFile.getName().endsWith("_ESTest.java")) {
                        // Run the instrumentation on the evosuite test files.
                        cu.findAll(CompilationUnit.class).stream().forEach(new ImportInstrumenter()::instrument);
                        cu.findAll(CompilationUnit.class).stream().forEach(new TestCaseInstrumenter()::instrument);
                    }

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
                File[] reportingFiles = new File(reportingPath).listFiles(file -> file.getName().endsWith(".java"));
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
                        if (p.exitValue() != 0) {
                            System.err.println("JUnit exited with non-zero exit code.");
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

                // Parse the daikon output, store the invariants, and check for fixed point.
                // TODO: Check fixed point here.

            } while (!fixedPointReached());

        } catch (ArgumentParserException e) {
            argParser.handleError(e);
            System.exit(1);
        }
    }

    private static String[] getDatagenClassPath() {
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);
        return classpathEntries;
    }

    private static boolean fixedPointReached() {
        // Dummy implementation for now.
        // Always returns false.
        return true;
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
                System.out.println("JUnit jar found in classpath: " + classPathAbsolute);
                return Optional.of(classPathAbsolute);
            }
        }

        return Optional.empty();
    }
}
