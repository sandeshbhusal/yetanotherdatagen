package edu.boisestate.datagen.utils;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class Compiler {
    public static void compile(String sourcePath, String outputPath, String... classPaths) {
        // Ensure sourcePath is a directory and exists
        File sourceDir = new File(sourcePath);
        if (!sourceDir.isDirectory()) {
            System.err.println("Source path is not a directory.");
            System.exit(1);
        }
        if (!sourceDir.exists()) {
            System.err.println("Source path does not exist.");
            System.exit(1);
        }

        // Ensure outputPath is a directory and create it if it does not exist
        File outputDir = new File(outputPath);
        if (!outputDir.isDirectory()) {
            if (!outputDir.mkdirs()) {
                System.err.println("Could not create output directory.");
                System.exit(1);
            }
        }

        // Get the Java compiler
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        if (compiler == null) {
            System.err.println("No Java compiler available.");
            System.exit(1);
        }

        // Set up the file manager
        StandardJavaFileManager fileManager = compiler.getStandardFileManager(null, null, null);
        Iterable<? extends JavaFileObject> compilationUnits = fileManager.getJavaFileObjects(sourceDir.listFiles(file -> file.getName().endsWith(".java")));

        // Set up the compilation options
        List<String> options = new ArrayList<>();
        if (classPaths.length > 0) {
            String classPath = String.join(File.pathSeparator, classPaths);
            options.add("-classpath");
            options.add(classPath);
        }

        // Specify the output directory
        options.add("-d");
        options.add(outputPath);

        // Compile for Java 11
        options.add("-source");
        options.add("11");
        options.add("-target");
        options.add("11");

        // Create a compiler task
        JavaCompiler.CompilationTask task = compiler.getTask(null, fileManager, null, options, null, compilationUnits);

        // Compile the code
        boolean success = task.call();
        if (!success) {
            System.err.println("Compilation failed.");
            System.exit(1);
        }

        // Close the file manager
        try {
            fileManager.close();
        } catch (Exception e) {
            System.err.println("Error closing file manager: " + e.getMessage());
        }
    }

    public static void main(String[] args) {
        compile("/tmp/sources/", "/tmp/compiled/");
    }
}
