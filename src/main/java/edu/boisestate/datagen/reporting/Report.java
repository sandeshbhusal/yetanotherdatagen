package edu.boisestate.datagen.reporting;

import edu.boisestate.datagen.reporting.InstrumentationRecord.RecordType;
import edu.boisestate.datagen.rmi.DataPointServer;

import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.util.HashMap;

public class Report {
    public static void datagen_instrument(String Id, Object... args) {
        System.out.println("datagen_instrument");
        HashMap<String, Object> trace = new HashMap<>();
        for (int i = 0; i < args.length; i += 2) {
            trace.put(String.valueOf(args[i]), args[i + 1]);
        }

        InstrumentationRecord record = new InstrumentationRecord(RecordType.INSTRUMENTATION, Id, trace);
        sendDataPoint(record);
    }

    public static void datagen_guard_instrument(String Id, Object... args) {
        System.out.println("datagen_guard_instrument");
        HashMap<String, Object> trace = new HashMap<>();
        for (int i = 0; i < args.length; i += 2) {
            trace.put(String.valueOf(args[i]), args[i + 1]);
        }

        InstrumentationRecord record = new InstrumentationRecord(RecordType.GUARD, Id, trace);
        sendDataPoint(record);
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

            server.receiveDataPoint(record);
            System.out.println("Data point sent to server");
        } catch (Exception e) {
            // Handle other exceptions that might occur
            System.err.println("Unexpected error during privileged action");
            e.printStackTrace();
        }
    }
}
