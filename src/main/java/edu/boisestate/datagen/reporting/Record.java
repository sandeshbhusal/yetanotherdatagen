package edu.boisestate.datagen.reporting;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Optional;

import org.tinylog.Logger;

public class Record implements Serializable {
    private static final long serialVersionUID = 0x0decaf;

    public String className;
    public String methodName;
    public String condition;
    public boolean pathTaken;
    public HashMap<String, Object> trace;

    public Record() {
    } // Need this for partial initialization. Can't have final types.

    // Default constructor with all fields.
    public Record(String className, String methodName, String condition, String variableNames, boolean pathTaken,
            HashMap<String, Object> trace) {
        this.className = className;
        this.methodName = methodName;
        this.condition = condition;
        this.pathTaken = pathTaken;
        this.trace = trace;
    }

    // Constructor that is useful to generate a key.
    public Record(String className, String methodName, String condition, String variableNames, boolean pathTaken) {
        this.className = className;
        this.methodName = methodName;
        this.condition = condition;
        this.pathTaken = pathTaken;
        this.trace = new HashMap<>();
    }

    public List<String> getVariablesInTrace() {
        return new ArrayList<>(trace.keySet());
    }

    public String genPathKey() {
        return Record.generateKeyForMap(className, methodName, condition, pathTaken);
    }

    public static String generateKeyForMap(String className, String methodName, String condition, boolean pathTaken) {
        StringBuilder sb = new StringBuilder();

        sb.append(className);
        sb.append(methodName);
        sb.append(condition);
        sb.append(pathTaken);
        return sb.toString();
    }

    public String genVariableKey(String variable) {
        if (trace.containsKey(variable)) {
            return className + methodName + condition + pathTaken + variable;
        } else {
            Logger.error("Cannot produce variable key for variable {}", variable);
            return null;
        }
    }

    public <T> Optional<T> getValue(String variable, Class<T> clazz) {
        try {
            if (this.trace.get(variable) == null) {
                Logger.error("Variable {} not found in trace", variable);
                return Optional.empty();
            } else {
                return Optional.of(clazz.cast(this.trace.get(variable)));
            }
        } catch (ClassCastException e) {
            System.err.println("Failed to cast value to " + clazz.getName());
            return Optional.empty();
        }
    }

    @Override
    public String toString() {
        // Make a pretty string
        // Specially with the trace, print it out as a map nicely.
        StringBuilder sb = new StringBuilder();

        sb.append(className);
        sb.append(methodName);
        sb.append(condition);
        sb.append(pathTaken);
        sb.append(trace);

        return sb.toString();
    }
}