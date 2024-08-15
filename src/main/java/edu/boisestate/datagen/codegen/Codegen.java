package edu.boisestate.datagen.codegen;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import edu.boisestate.datagen.server.Cache;

public class Codegen {
    // Generate code file for a given path, and put it into the specified directory.
    public static void generateCode(String filePath) {
        System.err.println("Generating code...");
        for (String pathKey : Cache.codeCache.keySet()) {
            System.err.println("Generating code for " + pathKey);
            String fileName = sanitizeStringForFileSystem(pathKey);
            StringBuilder sb = new StringBuilder();
            ArrayList<String> code = Cache.codeCache.get(pathKey);
            System.err.println("Generating code file with contents: " + code);

            File destFile = new File(filePath + File.separator + fileName + ".java");
            try {
                destFile.createNewFile();
            } catch (Exception e) {
                e.printStackTrace();
            }

            sb.append("public class " + sanitizeStringForFileSystem(fileName) + "{\n");
            sb.append("public static void main(String[] args) {\n");
            for (String testcase : code) {
                sb.append(testcase);
            }
            sb.append("}\n");
            sb.append("}");

            try {
                FileWriter fw = new FileWriter(destFile);
                fw.write(sb.toString());
                fw.close();
            } catch (IOException e) {
                System.err.println("Failed to write to file " + destFile.getName());
                // Crash.
                System.exit(1);
            }
        }
    }

    public static String sanitizeStringForFileSystem(String str) {
        // Replace the equality signs with eq, etc.
        str = str.replaceAll("<", "lt").replaceAll(">", "gt").replaceAll("==", "eq").replaceAll("!=", "neq");
        return str.replaceAll("[^a-zA-Z0-9]", "_");
    }
}
