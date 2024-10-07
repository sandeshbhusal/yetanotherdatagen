package edu.boisestate.datagen.utils;

import java.io.File;
import java.io.IOException;

import org.apache.commons.lang3.StringUtils;

public class ClassPathUtils {
    public static String[] getClassPath() {
        String classpath = System.getProperty("java.class.path");
        String[] classpathEntries = classpath.split(File.pathSeparator);
        return classpathEntries;
    }

    public static String getBinaryPath(String binaryName) {
        String[] command = {
            "which",
            binaryName
        };

        // Run the command and get the output.
        ProcessBuilder pb = new ProcessBuilder(command);
        pb.redirectErrorStream(true);

        try {
			Process p = pb.start();
			p.waitFor();

			// Read the output.
			java.io.InputStream is = p.getInputStream();
			java.io.BufferedReader reader = new java.io.BufferedReader(new java.io.InputStreamReader(is));
			String line = reader.readLine();
			return StringUtils.chomp(line.strip());

		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
			return null;
		}
    }
}
