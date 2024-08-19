package edu.boisestate.datagen.utils;

import java.io.File;

public class ClassPathUtils {
    public static String[] getClassPath() {
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);
        return classpathEntries;
    }
}