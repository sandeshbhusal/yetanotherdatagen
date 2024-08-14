package edu.boisestate.datagen.server;

import java.util.ArrayList;
import java.util.HashMap;

import edu.boisestate.datagen.reporting.Record;

// Cache is a singleton class.
public class Cache {
    private static Cache instance = null;

    // HashMap that stores the code for each path.
    // Maps from a path key to a list of code strings that executed that code path.
    private static HashMap<String, ArrayList<String>> codeCache = new HashMap<String, ArrayList<String>>();

    // HashMap that maps each execution path to a map of variables to the values those variables took.
    private static HashMap<String, ArrayList<Record>> dataCache = new HashMap<String, ArrayList<Record>>();

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
        String key = record.toStringKey();
        ArrayList<String> code = codeCache.getOrDefault(key, new ArrayList<>());
        code.add(record.toString());

        // Add the record to the data cache.
        // The key is changed here to include the variable name.
        // TODO: This is a massive code smell. Need to refactor this heavily later.
        ArrayList<Record> data = dataCache.getOrDefault(key+record.variableNames, new ArrayList<>());
        data.add(record);
    }

    public ArrayList<Record> getDataPointsForAVariable(
        String className,
        String methodName,
        String condition,
        String variableName
    ){
        Record tempRecord = new Record();
        tempRecord.className = className;
        tempRecord.methodName = methodName;
        tempRecord.condition = condition;
        
        tempRecord.pathTaken = true;
        String trueKeyString = tempRecord.toStringKey();

        tempRecord.pathTaken = false;
        String falseKeyString = tempRecord.toStringKey();

        ArrayList<Record> trueData = dataCache.getOrDefault(trueKeyString+variableName, new ArrayList<>());
        ArrayList<Record> falseData = dataCache.getOrDefault(falseKeyString+variableName, new ArrayList<>());

        trueData.addAll(falseData);
        return trueData;
    }
}
