package edu.boisestate.datagen.server;

import java.util.ArrayList;
import java.util.HashMap;

import edu.boisestate.datagen.reporting.InstrumentationRecord;

public class NewCache {
    private static NewCache instance = null;
    private static HashMap<String, ArrayList<HashMap<String, Object>>> dataCache = new HashMap<>();

    public static NewCache getInstance() {
        if (instance == null) {
            instance = new NewCache();
        }
        return instance;
    }

    public void addDataPoint(InstrumentationRecord record) {
        // Get key.
        String key = record.getRecordId();

        // Insert into cache.
        ArrayList<HashMap<String, Object>> data = dataCache.getOrDefault(key, new ArrayList<>());
        data.add(record.getValues());
        dataCache.put(key, data);
    }
}
