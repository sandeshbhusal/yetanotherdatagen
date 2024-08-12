package edu.boisestate.datagen.utils;

import java.io.File;

public class FileOps {
    // Function to create a directory if not exists, if exists, recursively delete contents.
    public void createDirectory(String path) {
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
}
