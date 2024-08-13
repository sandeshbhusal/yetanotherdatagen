package edu.boisestate.datagen;

import java.io.File;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.IfStatementInstrumenter;
import edu.boisestate.datagen.instrumenters.ImportInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.utils.FileOps;
import net.sourceforge.argparse4j.*;
import net.sourceforge.argparse4j.inf.ArgumentParser;
import net.sourceforge.argparse4j.inf.ArgumentParserException;
import net.sourceforge.argparse4j.inf.Namespace;

public class App {
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

        try {
            // Parse the arguments.
            Namespace ns = argParser.parseArgs(args);
            String source = ns.getString("source");
            String workdir = ns.getString("workdir");

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
            String augmentedPath = workdir + "/instrumented/augmented";
            String reportingPath = workdir + "/instrumented/reporting";
            String compiledPath = workdir + "/compiled";

            FileOps fileOps = new FileOps();
            fileOps.createDirectory(augmentedPath);
            fileOps.createDirectory(reportingPath);
            fileOps.createDirectory(compiledPath);

            // Find all .java files in the source directory.
            File[] javaFiles = sourceDir.listFiles(file -> file.getName().endsWith(".java"));

            for (File javaFile : javaFiles) {
                // Print file contents.
                File file = new File(javaFile.getAbsolutePath());
                System.out.println("File: " + file.getName());

                String contents = FileOps.readFile(file);
                JavaParser parser = new JavaParser();
                CompilationUnit cu = parser.parse(contents).getResult().orElseThrow();

                ImportInstrumenter importInstrumenter = new ImportInstrumenter();
                IfStatementInstrumenter ifInstrumenter = new IfStatementInstrumenter(InstrumentationMode.INSTRUMENTATION,
                        null);

                cu.findAll(CompilationUnit.class).stream().forEach(importInstrumenter::instrument);
                cu.findAll(CompilationUnit.class).stream().forEach(ifInstrumenter::instrument);

                // Print cu.
                System.out.println(cu.toString());
            }

        } catch (ArgumentParserException e) {
            argParser.handleError(e);
            System.exit(1);
        }
    }

    public static void addReportingMethods(CompilationUnit cu) {
    }
}
