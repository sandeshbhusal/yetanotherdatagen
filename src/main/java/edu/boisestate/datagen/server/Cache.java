package edu.boisestate.datagen.server;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import edu.boisestate.datagen.reporting.Record;

// Cache is a singleton class.
public class Cache {
    private static Cache instance = null;

    // HashMap that stores the code for each path.
    // Maps from a path key to a list of code strings that executed that code path.
    // Use a hashset instead of an arraylist to avoid duplicates.
    public static HashMap<String, HashSet<String>> codeCache = new HashMap<String, HashSet<String>>();

    // HashMap that maps each execution path to a map of variables to the values
    // those variables took.
    public static HashMap<String, ArrayList<Record>> dataCache = new HashMap<String, ArrayList<Record>>();

    private Cache() {
    }

    public static Cache getInstance() {
        if (instance == null) {
            instance = new Cache();
        }
        return instance;
    }

    public void addDataPoint(String testcase, Record record) {
        // Add this testcase to the code cache.
        String key = record.genPathKey();
        HashSet<String> code = codeCache.getOrDefault(key, new HashSet<>());
        testcase = testcase.replaceAll("assert.*;", "");
        code.add(testcase);
        codeCache.put(key, code);

        // Add the record to the data cache.
        // The key is changed here to include the variable name.
        // Add this trace group to the path key.
        String variableKeyString = record.genPathKey();
        ArrayList<Record> data = dataCache.getOrDefault(variableKeyString, new ArrayList<>());
        data.add(record);
        dataCache.put(variableKeyString, data);
    }

    public HashSet<String> getCodeForPath(String className, String methodName, String condition, boolean pathTaken) {
        // Refactor this later.
        Record tempRecord = new Record();
        tempRecord.className = className;
        tempRecord.methodName = methodName;
        tempRecord.condition = condition;
        tempRecord.pathTaken = pathTaken;
        String key = tempRecord.genPathKey();
        return codeCache.getOrDefault(key, new HashSet<>());
    }

    public ArrayList<Record> getDataPointsForPath(
            String className,
            String methodName,
            String condition,
            boolean pathTaken) {
        String key = Record.generateKeyForMap(className, methodName, condition, pathTaken);
        return dataCache.getOrDefault(key, new ArrayList<>());
    }

    public ArrayList<Record> getDataPointsForAVariable(
            String className,
            String methodName,
            String condition,
            boolean pathTaken,
            String variableName) {
        Record tempRecord = new Record();
        tempRecord.className = className;
        tempRecord.methodName = methodName;
        tempRecord.condition = condition;
        tempRecord.pathTaken = pathTaken;

        tempRecord.pathTaken = true;
        String trueKeyString = tempRecord.genPathKey();

        tempRecord.pathTaken = false;
        String falseKeyString = tempRecord.genPathKey();

        ArrayList<Record> trueData = dataCache.getOrDefault(trueKeyString + variableName, new ArrayList<>());
        ArrayList<Record> falseData = dataCache.getOrDefault(falseKeyString + variableName, new ArrayList<>());

        trueData.addAll(falseData);
        return trueData;
    }
}
