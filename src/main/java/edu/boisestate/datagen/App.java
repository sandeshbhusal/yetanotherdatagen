package edu.boisestate.datagen;

import java.io.File;

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
        //    - A {{workdir}}/instrumented/augmented     contains the instrumented code with augmentations.
        //    - A {{workdir}}/instrumented/reporting     contains the code that will report the data to our lib.
        //    - A {{workdir}}/compiled/             contains the compiled instrumented code.

        ArgumentParser parser = ArgumentParsers.newFor("datagen").build()
                .description("DataGen is a tool for generating data-driven tests for Java programs.");

        parser.addArgument("-s", "--source")
                .help("The path to the source code file(s), This is a folder.")
                .required(true)
                .type(String.class);

        parser.addArgument("-w", "--workdir")
                .help("Working directory for datagen.")
                .required(true)
                .type(String.class);

        try {
            // Parse the arguments.
            Namespace ns = parser.parseArgs(args);
            String source  = ns.getString("source");
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
            FileOps fileOps = new FileOps();
            fileOps.createDirectory(workdir + "/instrumented/augmented");
            fileOps.createDirectory(workdir + "/instrumented/reporting");
            fileOps.createDirectory(workdir + "/compiled");

        } catch (ArgumentParserException e) {
            parser.handleError(e);
            System.exit(1);
        }
    }
}
