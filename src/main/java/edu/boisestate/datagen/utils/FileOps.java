package edu.boisestate.datagen.utils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

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

    public static void copyFile(File source, File destination) {
        try {
            Files.copy(source.toPath(), new FileOutputStream(destination));

        } catch (Exception e) {
            e.printStackTrace();
            System.err.println("Error copying file. Fatal");
            System.exit(-1);
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
        FileOutputStream fos = null;
        OutputStreamWriter osw = null;
        try {
            fos = new FileOutputStream(file);
            osw = new OutputStreamWriter(fos);
            osw.write(content);
            osw.flush(); // Ensure data is written to the buffer

            // Force synchronization with the file system.
            fos.getFD().sync();
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        } finally {
            try {
                if (osw != null) {
                    osw.close();
                }
                if (fos != null) {
                    fos.close();
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
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

    public static List<String> readFileLines(File file) {
        List<String> lines = new ArrayList<>();
        try {
            FileReader fr = new FileReader(file);
            BufferedReader br = new BufferedReader(fr);
            String line;
            while ((line = br.readLine()) != null) {
                lines.add(line);
            }
            br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return lines;
    }
}
