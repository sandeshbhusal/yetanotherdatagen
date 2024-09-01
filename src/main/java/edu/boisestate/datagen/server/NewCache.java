package edu.boisestate.datagen.server;

import java.util.ArrayList;
import java.util.HashMap;

import edu.boisestate.datagen.reporting.InstrumentationRecord;

public class NewCache {
    private static NewCache instance = null;
    public HashMap<String, ArrayList<HashMap<String, Object>>> instrumentation_cache = new HashMap<>();
    public HashMap<String, ArrayList<HashMap<String, Object>>> guard_cache = new HashMap<>();

    public static NewCache getInstance() {
        if (instance == null) {
            instance = new NewCache();
        }
        return instance;
    }

    public void add_instrumentation_data(InstrumentationRecord record) {
        // Get key.
        String key = record.getRecordId();

        // Insert into cache.
        ArrayList<HashMap<String, Object>> data = instrumentation_cache.getOrDefault(key, new ArrayList<>());
        data.add(record.getValues());
        instrumentation_cache.put(key, data);
    }
}
