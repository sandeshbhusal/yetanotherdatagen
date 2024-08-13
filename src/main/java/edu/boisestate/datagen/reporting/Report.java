package edu.boisestate.datagen.reporting;

public class Report {
    public static void reportMethodInvocation(String methodName, Object ... args) {
        System.out.println(methodName);
    }

    public static void reportDataPoint(String dataPointName, Object ... value) {
        System.out.println(dataPointName);
    }
}
