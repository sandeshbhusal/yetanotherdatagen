package edu.boisestate.datagen.reporting;

import edu.boisestate.datagen.reporting.InstrumentationRecord.RecordType;
import edu.boisestate.datagen.rmi.DataPointServer;

import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.util.HashMap;

public class Report {
    public static int datagen_remote_port;

    public static void datagen_instrument(int port, String Id, Object... args) {
        datagen_remote_port = port;
        HashMap<String, Object> trace = new HashMap<>();
        for (int i = 0; i < args.length; i += 2) {
            trace.put(String.valueOf(args[i]), args[i + 1]);
        }

        InstrumentationRecord record = new InstrumentationRecord(RecordType.INSTRUMENTATION, Id, trace);
        sendDataPoint(record);
    }

    public static void datagen_guard_instrument(int port, String Id, Object... args) {
        datagen_remote_port = port;
        HashMap<String, Object> trace = new HashMap<>();
        for (int i = 0; i < args.length; i += 2) {
            trace.put(String.valueOf(args[i]), args[i + 1]);
        }

        InstrumentationRecord record = new InstrumentationRecord(RecordType.GUARD, Id, trace);
        sendDataPoint(record);
    }

    public static void sendDataPoint(InstrumentationRecord record) {
        int datagen_instance_id = datagen_remote_port;
        try {
            if (datagen_instance_id == 0) {
                System.err.println("Something is severely wrong. Port is 0.");
                System.exit(1);
            }
            // print datapoint server name.
            System.out.println(String.format("DataPointServer_" + datagen_instance_id));

            DataPointServer server = (DataPointServer) LocateRegistry.getRegistry()
                    .lookup(String.format("DataPointServer_%d", datagen_instance_id));

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
            System.exit(1);
        }
    }
}
