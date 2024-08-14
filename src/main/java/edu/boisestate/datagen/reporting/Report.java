package edu.boisestate.datagen.reporting;

import edu.boisestate.datagen.rmi.DataPointServer;

import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;

public class Report {

    private static String testCaseBody = null;

    public static void reportDataPoint(
            String className,
            String methodName,
            String condition,
            boolean pathTaken,
            Object... args) {
        System.out.println("Reporting data point");
        System.out.println("There are " + args.length / 2 + " variables to report");

        Record record = new Record();
        record.className = className;
        record.methodName = methodName;
        record.condition = condition;
        record.pathTaken = pathTaken;

        int i = 0;
        for (Object arg : args) {
            if (i % 2 == 0) {
                record.variableNames = arg.getClass().getName();
            } else {
                record.variableValues = arg;

                try {
                    System.out.println("Attaching to server");

                    DataPointServer server = (DataPointServer) LocateRegistry.getRegistry()
                            .lookup("DataPointServer");
                    Registry registry = LocateRegistry.getRegistry();
                    // Dump everything registered in the registry
                    for (String name : registry.list()) {
                        System.out.println("Registry entry: " + name);
                    }

                    server.receiveDataPoint(testCaseBody, record);
                    System.out.println("Data point sent to server");
                } catch (Exception e) {
                    // Handle other exceptions that might occur
                    System.err.println("Unexpected error during privileged action");
                    e.printStackTrace();
                }
            }
            i += 1;
        }
    }

    public static void startTestCase(String tcBody) {
        System.out.println("Starting test case");
        testCaseBody = tcBody;
    }

    public static void endTestCase() {
        System.out.println("Ending test case");
        testCaseBody = null;
    }
}
