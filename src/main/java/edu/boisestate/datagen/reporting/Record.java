package edu.boisestate.datagen.reporting;

import java.util.Optional;

public class Record {
    public final String className;
    public final String methodName;
    public final String condition;
    public final boolean pathTaken;
    public final String variableNames;
    public final Object variableValues;

    // Default constructor with all fields.
    public Record(String className, String methodName, String condition, String variableNames, boolean pathTaken,
            Object variableValues) {
        this.className = className;
        this.methodName = methodName;
        this.condition = condition;
        this.pathTaken = pathTaken;
        this.variableNames = variableNames;
        this.variableValues = variableValues;
    }

    // Constructor that is useful to generate a key.
    public Record(String className, String methodName, String condition, String variableNames, boolean pathTaken) {
        this.className = className;
        this.methodName = methodName;
        this.condition = condition;
        this.pathTaken = pathTaken;
        this.variableNames = variableNames;
        this.variableValues = null;
    }

    // Override toString() to print the record in a format that can be used as a
    // key.
    public String toStringKey() {
        StringBuilder sb = new StringBuilder();

        sb.append(className);
        sb.append(methodName);
        sb.append(condition);
        sb.append(pathTaken);
        sb.append(variableNames);

        return sb.toString();
    }

    public <T> Optional<T> getValue(Class<T> clazz) {
        try {
            return Optional.of(clazz.cast(this.variableValues));
        } catch (ClassCastException e) {
            System.err.println("Failed to cast value to " + clazz.getName());
            return Optional.empty();
        }
    }
}
