package edu.boisestate.datagen.server;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
// import org.tinylog.Logger;

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

        // Logger.debug("Adding data point to cache " + record.toString());
        if (record.getRecordType() == InstrumentationRecord.RecordType.INSTRUMENTATION) {
            // Insert into instrumentation cache.
            ArrayList<HashMap<String, Object>> data = instrumentation_cache.getOrDefault(key, new ArrayList<>());
            data.add(record.getValues());
            instrumentation_cache.put(key, data);
        } else {
            // Insert into guard cache.
            ArrayList<HashMap<String, Object>> data = guard_cache.getOrDefault(key, new ArrayList<>());
            data.add(record.getValues());
            guard_cache.put(key, data);
        }
    }

    // TODO: This method needs to be updated with TABU, and Round-Robin data
    // returning methods.
    // so that we can split the same path in multiple ways.
    public List<HashMap<String, Object>> get_seen_guard_data(String guardId) {
        return this.guard_cache.get(guardId);
    }
}
