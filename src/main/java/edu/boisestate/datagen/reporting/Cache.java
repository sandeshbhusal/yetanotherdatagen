package edu.boisestate.datagen.reporting;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class Cache {
    private static Cache instance = null;
    public HashMap<String, HashSet<HashMap<String, Object>>> instrumentation_cache = new HashMap<>();
    public HashMap<String, HashSet<HashMap<String, Object>>> guard_cache = new HashMap<>();

    public static Cache getInstance() {
        if (instance == null) {
            instance = new Cache();
        }
        return instance;
    }

    public void add_instrumentation_data(InstrumentationRecord record) {
        // Get key.
        String key = record.getRecordId();

        // Logger.debug("Adding data point to cache " + record.toString());
        if (record.getRecordType() == InstrumentationRecord.RecordType.INSTRUMENTATION) {
            // Insert into instrumentation cache.
            HashSet<HashMap<String, Object>> data = instrumentation_cache.getOrDefault(key, new HashSet<>());
            data.add(record.getValues());
            instrumentation_cache.put(key, data);
        } else {
            // Insert into guard cache.
            HashSet<HashMap<String, Object>> data = guard_cache.getOrDefault(key, new HashSet<>());
            data.add(record.getValues());
            guard_cache.put(key, data);
        }
    }

    // TODO: This method needs to be updated with TABU, and Round-Robin data
    // returning methods.
    // so that we can split the same path in multiple ways.
    public List<HashMap<String, Object>> get_seen_guard_data(String guardId) {
        return Optional.ofNullable(this.guard_cache.get(guardId))
                .map(guardData -> guardData.stream()
                        .distinct()
                        .collect(Collectors.toList()))
                .orElse(null);
    }

    public HashMap<String, String> generate_daikon_dtraces() {
        // Start with every key, in the instrumentation cache hashmap.
        HashMap<String, String> traceFilesInstru = getTraceFilesForCache(this.instrumentation_cache);
        HashMap<String, String> traceFilesGuard = getTraceFilesForCache(this.guard_cache);

        // Return both, combined.
        traceFilesInstru.putAll(traceFilesGuard);
        return traceFilesInstru;
    }

    public HashMap<String, String> getTraceFilesForCache(HashMap<String, HashSet<HashMap<String, Object>>> cache) {
        HashMap<String, String> traceFiles = new HashMap<>();
        for (String key : instrumentation_cache.keySet()) {
            // Get the data for the key.
            HashSet<HashMap<String, Object>> data = instrumentation_cache.get(key);

            // Check empty.
            if (data.isEmpty()) {
                continue;
            }

            // Get the variable names.
            Set<String> variableNames = data.iterator().next().keySet();

            StringBuilder sb = new StringBuilder();
            sb.append("decl-version 2.0\n");
            sb.append("var-comparability none\n\n");
            sb.append("ppt Faker.fakemethod(int");
            // At least one int required.
            for (int k = 0; k < variableNames.size() - 1; k++) {
                sb.append(",\\_int");
            }
            sb.append("):::DATAGEN\n");
            sb.append("ppt-type enter\n");

            // For now only int variables are supported
            for (String variableName : variableNames) {
                sb.append("variable ");
                sb.append(variableName);
                sb.append("\n");
                sb.append("  var-kind variable\n");
                sb.append("  dec-type int\n");
                sb.append("  rep-type int\n");
                sb.append("  flags is_param\n");
                sb.append("  comparability 22\n");
            }
            sb.append("\n");

            for (HashMap<String, Object> dat : data) {
                sb.append("Faker.fakemethod(int");
                for (int _k = 0; _k < variableNames.size() - 1; _k++) {
                    sb.append(",\\_int");
                }
                sb.append("):::DATAGEN\n");
                sb.append("this_invocation_nonce\n");
                // For every variable, insert the value,
                // start with and end with 1, like: 1\nvarname\nvalue
                for (String _k : variableNames) {
                    sb.append("1\n");
                    sb.append(_k);
                    sb.append("\n");
                    sb.append(dat.get(_k));
                    sb.append("\n");
                }
                sb.append("1\n");
                sb.append("\n");
            }
            traceFiles.put(key, sb.toString());
        }
        return traceFiles;
    }
}
