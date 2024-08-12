package edu.boisestate.datagen.utils;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class Compiler {
    public static void compile(String sourceFilePath, String outputPath, String... classPaths) {
        // Ensure sourceFilePath is a file and exists
        File sourceFile = new File(sourceFilePath);
        if (!sourceFile.isFile()) {
            System.err.println("Source path is not a file.");
            System.exit(1);
        }
        if (!sourceFile.exists()) {
            System.err.println("Source file does not exist.");
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
        Iterable<? extends JavaFileObject> compilationUnits = fileManager.getJavaFileObjects(sourceFile);

        // Set up the compilation options
        List<String> options = new ArrayList<>();
        
        // Add the base directory of the source file to the classpath
        String baseDir = sourceFile.getParent();
        if (baseDir != null && !baseDir.isEmpty()) {
            options.add("-classpath");
            options.add(baseDir);
        }
        
        // Add any additional class paths
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
        // Example usage: compile a single file
        compile("/tmp/sources/MyClass.java", "/tmp/compiled/");
    }
}
