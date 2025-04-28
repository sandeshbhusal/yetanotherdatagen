package edu.boisestate.datagen.reporting;

import java.util.HashMap;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.tinylog.Logger;

import java.util.Random;

public class Cache {
    private static Cache instance = null;
    public HashMap<String, HashSet<HashMap<String, Object>>> instrumentation_cache = new HashMap<>();
    public HashMap<String, HashSet<HashMap<String, Object>>> guard_cache = new HashMap<>();
    public HashMap<String, HashMap<String, Object>> seen_sent = new HashMap<>();

    // Keep track of which code paths were actually exercised in the last run.
    public HashMap<String, Integer> wasTargeted = new HashMap<>();

    public static Cache getInstance() {
        if (instance == null) {
            instance = new Cache();
        }
        return instance;
    }

    public List<String> getInstrumentationCacheKeys() {
        ArrayList<String> rval = new ArrayList<>();
        rval.addAll(this.instrumentation_cache.keySet());
        return rval;
    }

    // Reset information about which branches were targeted.
    public void resetTargetedInformation() {
        this.wasTargeted.clear();
    }

    public HashMap<String, Integer>  getAllTargetsVisited() {
        return this.wasTargeted;
    }

    // Check if this key was targeted in the last iteration.
    public boolean wasTargeted(String key) {
        int hitcount = this.wasTargeted.getOrDefault(key, 0);
        return hitcount > 0;
    }

    public void add_instrumentation_data(InstrumentationRecord record) {
        // Get key.
        String key = record.getRecordId();

        // This key was targeted.
        wasTargeted.put(key, wasTargeted.getOrDefault(key, 0) + 1);

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

    public List<HashMap<String, Object>> get_seen_guard_data(String guardId, boolean optimize) {
        if (optimize) {
            return get_seen_guard_data_optimized(guardId);
        } else {
            return get_seen_guard_data_full(guardId);
        }
    }

    private List<HashMap<String, Object>> get_seen_guard_data_full(String guardId) {
        ArrayList<HashMap<String, Object>> cacheData = new ArrayList<>();
        cacheData.addAll(guard_cache.getOrDefault(guardId, new HashSet<HashMap<String, Object>>()));
        return cacheData;
    }

    // so that we can split the same path in multiple ways.
    private List<HashMap<String, Object>> get_seen_guard_data_optimized(String guardId) {
        // With some probability, return a random sample of the data.
        // The data points may not have the same number of variables.
        HashSet<HashMap<String, Object>> data = guard_cache.get(guardId);
        if (data == null) {
            return null;
        }

        // Since all variables will be the same, we can convert the hashset, to
        // a hashmap of hashsets.
        HashMap<String, HashSet<Object>> observations = new HashMap<>();
        for (HashMap<String, Object> datum : data) {
            for (String variable : datum.keySet()) {
                HashSet<Object> observation = observations.getOrDefault(variable, new HashSet<>());
                observation.add(datum.get(variable));
                observations.put(variable, observation);
            }
        }

        // At this point, we have the values recorded for each variable.
        // We now calculate the value that has the least standard deviation
        // Asssuming all values are integers.
        Float minsdValue = Float.MAX_VALUE;
        String minsdVariable = null;
        for (String variable : observations.keySet()) {
            HashSet<Object> observation = observations.get(variable);
            Float sd = calculateStandardDeviation(observation);
            if (sd < minsdValue) {
                minsdValue = sd;
                minsdVariable = variable;
            }
        }

        // We have the variable with the least SD. Now we return a random sample of
        // that variable, including half the datapoinnts we saw previously. If the
        // dataset size is too small, we return the entire dataset, when n <= 4.
        // (Heuristics later)
        int n = observations.get(minsdVariable).size();
        ArrayList<HashMap<String, Object>> sampled = new ArrayList<>();
        Iterator<Object> it = observations.get(minsdVariable).iterator();
        if (n <= 4) {
            // Put everything from the iterator into a list.
            while (it.hasNext()) {
                HashMap<String, Object> datum = new HashMap<>();
                datum.put(minsdVariable, it.next());
                sampled.add(datum);
            }
            return sampled;

        } else {
            // Sample datapoints with 50% probability and return them
            for (int i = 0; i < n; i++) {
                Float select = (new Random()).nextFloat();
                if (select < 0.5f) {
                    HashMap<String, Object> datum = new HashMap<>();
                    datum.put(minsdVariable, it.next());
                    sampled.add(datum);
                }
            }
            return sampled;
        }
    }

    public Float calculateStandardDeviation(HashSet<Object> observation) {
        // Calculate the mean.
        Integer sum = 0;
        for (Object o : observation) {
            // WARN: Only works with Ints for now.
            sum += (Integer) o;
        }

        Float mean = (float) sum / observation.size();

        // Calculate the variance.
        Float variance = 0.0f;
        for (Object o : observation) {
            Float diff = ((Integer) o).floatValue() - mean;
            variance += diff * diff;
        }
        variance /= observation.size();

        return (float) Math.sqrt(variance);
    }

    public HashMap<String, String> generate_daikon_dtraces() {
        // Start with every key, in the instrumentation cache hashmap.
        HashMap<String, String> traceFilesInstru = getTraceFilesForCache(this.instrumentation_cache);
        Logger.info("Generated " + traceFilesInstru.size() + " Daikon trace files for instrumentation data.");
        return traceFilesInstru;
    }

    public HashMap<String, String> generate_dig_traces() {
        // Start with every key, in the instrumentation cache hashmap.
        HashMap<String, String> traceFiles = generate_dig_files(this.instrumentation_cache);
        Logger.info("Generated " + traceFiles.size() + " DiG trace files for instrumentation data.");
        return traceFiles;
    }

    public HashMap<String, String> generate_dig_files(HashMap<String, HashSet<HashMap<String, Object>>> cache) {
        HashMap<String, String> traceFiles = new HashMap<>();
        for (String key : cache.keySet()) {
            StringBuilder sb = new StringBuilder();
            sb.append("vtrace1");

            // Get the variable names.
            Set<String> variableNames = cache.get(key).iterator().next().keySet();

            for (String variableName : variableNames) {
                sb.append("; I " + variableName);
            }
            sb.append("\n");

            // Get the data for the key.
            HashSet<HashMap<String, Object>> data = cache.get(key);

            // Check empty.
            if (data.isEmpty()) {
                continue;
            }

            for (HashMap<String, Object> dat : data) {
                sb.append("vtrace1");
                for (String variableName : variableNames) {
                    sb.append("; " + dat.get(variableName));
                }
                sb.append("\n");
            }

            traceFiles.put(key, sb.toString());
        }

        return traceFiles;
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
