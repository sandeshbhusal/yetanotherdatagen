package edu.boisestate.datagen;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;

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

        try {
            // Parse the arguments.
            Namespace ns = argParser.parseArgs(args);
            source = ns.getString("source");
            workdir = ns.getString("workdir");

            String evosuiteJarPath = ns.getString("evosuite");
            if (evosuiteJarPath == null && !evosuitePresentInClassPath()) {
                System.err.println("Evosuite jar file not provided, and evosuite is not present in the classpath.");
                System.err.println("Provide the evosuite jar path using the -e flag.");
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
                    Compiler.compile(file.getAbsolutePath(), compiledPath, getRunningClassPath());
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

                    if (evosuitePresentInClassPath() || evosuiteJarPath != null) {
                        String jarPath = null;

                        // Precedence is given to the evosuite jar path provided by the user.
                        if (evosuiteJarPath != null) {
                            jarPath = evosuiteJarPath;

                        } else {
                            // Evosuite was in the classpath, find the jar file for it.
                            String[] classpathEntries = System.getProperty("java.class.path").split(File.pathSeparator);
                            for (String classpathEntry : classpathEntries) {
                                // We run the evosuite jar, not the runtime jar.
                                if (classpathEntry.contains("evosuite") && !classpathEntry.contains("runtime")) {
                                    jarPath = classpathEntry;
                                    break;
                                }
                            }
                        }

                        // Build a prcess builder to run evosuite.
                        ProcessBuilder pb = new ProcessBuilder("java", "-jar", jarPath, "-projectCP",
                                compiledFiles.getAbsolutePath(),
                                "-class", className, "-Dcriterion=BRANCH");
                        pb.redirectErrorStream(true);
                        try {
                            Process p = pb.start();
                            // print the output of the process
                            BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
                            String line;
                            while ((line = reader.readLine()) != null) {
                                System.out.println(line);
                            }
                            p.waitFor();
                            // Check the exit code of the process.
                            if (p.exitValue() != 0) {
                                System.err.println("Evosuite exited with non-zero exit code.");
                                System.exit(1);
                            }
                        } catch (IOException | InterruptedException e) {
                            e.printStackTrace();
                            System.exit(1);
                        }
                    }
                    System.out.println("Finished running evosuite.");
                }

                // Now, instrument the evosuite testcases with method invocation
                // instrumentation.
                // Evosuite tests are generated in the $PWD/evosuite-tests folder.

                String evosuiteTestsPath = "./evosuite-tests";
                File evosuiteTests = new File(evosuiteTestsPath);
                File[] evosuiteTestsFiles = evosuiteTests.listFiles(file -> file.getName().endsWith(".java"));
                if (evosuiteTestsFiles == null) {
                    System.err.println("No evosuite tests were generated.");
                    System.exit(1);
                }

                // Instrument the evosuite test file with method invocation.
                for (File evosuiteTestFile : evosuiteTestsFiles) {
                    String contents = FileOps.readFile(evosuiteTestFile);
                    JavaParser parser = new JavaParser();
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

                    // Compile the evosuite test file along with the compiled files
                    // from the source directory, so that we can run them on it.
                    ArrayList<String> classPaths = new ArrayList<>();
                    classPaths.addAll(Arrays.asList(getRunningClassPath()));
                    classPaths.add(compiledPath);

                    Compiler.compile(file.getAbsolutePath(), compiledPath, classPaths.toArray(String[]::new));
                }

                // Run the compiled evosuite tests along with source classfiles on daikon,
                // so that we can get the invariants from Daikon.
                // TODO: Run daikon here.

                // Parse the daikon output, store the invariants, and check for fixed point.
                // TODO: Check fixed point here.

            } while (!fixedPointReached());

        } catch (ArgumentParserException e) {
            argParser.handleError(e);
            System.exit(1);
        }
    }

    private static String[] getRunningClassPath() {
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);

        ArrayList<String> classpathEntriesExt = new ArrayList<>();
        classpathEntriesExt.add(compiledPath);
        return classpathEntries;
    }

    private static boolean fixedPointReached() {
        // Dummy implementation for now.
        // Always returns false.
        return true;
    }

    private static boolean evosuitePresentInClassPath() {
        // Checks if evosuite is present in the classpath.
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);

        for (String classpathEntry : classpathEntries) {
            if (classpathEntry.contains("evosuite")) {
                System.out.println("Evosuite jar found in classpath.");
                return true;
            }
        }

        return false;
    }
}
