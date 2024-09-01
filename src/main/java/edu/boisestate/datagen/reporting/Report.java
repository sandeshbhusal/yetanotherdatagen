package edu.boisestate.datagen.reporting;

import edu.boisestate.datagen.rmi.DataPointServer;

import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.util.HashMap;

public class Report {

    private static String testCaseBody = null;

    public static void datagen_instrument(String Id, Object... args) {
        HashMap<String, Object> trace = new HashMap<>();
        for (int i = 0; i < args.length; i += 2) {
            trace.put(String.valueOf(args[i]), args[i + 1]);
        }

        InstrumentationRecord record = new InstrumentationRecord(Id, trace);
        sendDataPoint(record);
    }

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
        record.trace = new HashMap<>();

        for (int i = 0; i < args.length; i += 2) {
            record.trace.put(String.valueOf(args[i]), args[i + 1]);
        }

        sendDataPoint(record);
    }

    public static void sendDataPoint(Record record) {
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

    public static void sendDataPoint(InstrumentationRecord record) {
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

    public static void startTestCase(String tcBody) {
        System.out.println("Starting test case");
        testCaseBody = tcBody;
    }

    public static void endTestCase() {
        System.out.println("Ending test case");
        testCaseBody = null;
    }
}
