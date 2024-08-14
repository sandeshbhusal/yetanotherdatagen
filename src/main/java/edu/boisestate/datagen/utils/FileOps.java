package edu.boisestate.datagen.utils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;

public class FileOps {
    public static void createDirectory(String path) {
        File file = new File(path);
        if (!file.exists()) {
            file.mkdirs();
        } else {
            File[] files = file.listFiles();
            for (File f : files) {
                f.delete();
            }

            file.mkdirs();
        }
    }

    public static String readFile(File file) {
        StringBuilder sb = new StringBuilder();
        try {
            FileReader fr = new FileReader(file);
            BufferedReader br = new BufferedReader(fr);
            String line;
            while ((line = br.readLine()) != null) {
                sb.append(line);
                sb.append("\n");
            }
            br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return sb.toString();
    }

    public static void writeFile(File file, String content) {
        try {
            FileWriter fw = new FileWriter(file);
            fw.write(content);
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    public static void recursivelyCopyFolder(File sourceFolder, File destinationFolder) {
        if (sourceFolder.isDirectory()) {
            destinationFolder.mkdirs();
            for (File child : sourceFolder.listFiles()) {
                recursivelyCopyFolder(child, new File(destinationFolder, child.getName()));
            }
        } else {
            try {
                Files.copy(sourceFolder.toPath(), destinationFolder.toPath());
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }
    }

    public static void recursivelyDeleteFolder(File folder) {
        if (folder.isDirectory()) {
            for (File file : folder.listFiles()) {
                recursivelyDeleteFolder(file);
            }
        } else {
            folder.delete();
        }
    }
}
