package edu.boisestate.datagen.reporting;

public class Report {
    private static String testCaseBody = null;

    public static void reportDataPoint(String dataPointName, Object ... value) {
        System.out.println("Data point report");
        System.out.println(dataPointName);
    }

    public static void startTestCase(String tcBody) {
        System.out.println("Starting testcase");
        testCaseBody = tcBody;
    }

    public static void endTestCase() {
        System.out.println("Ending testcase");
        testCaseBody = null;
    }
}
