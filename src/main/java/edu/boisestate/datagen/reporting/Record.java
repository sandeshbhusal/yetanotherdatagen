package edu.boisestate.datagen.reporting;

import java.io.Serializable;
import java.util.Optional;

public class Record implements Serializable {
    private static final long serialVersionUID = 0x0decaf;

    public String className;
    public String methodName;
    public String condition;
    public boolean pathTaken;
    public String variableNames;
    public Object variableValues;

    public Record() {
    } // Need this for partial initialization. Can't have final types.

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

    public String genPathKey() {
        return className + methodName + condition + pathTaken;
    }

    public String genVariableKey() {
        return className + methodName + condition + pathTaken + variableNames;
    }

    public <T> Optional<T> getValue(Class<T> clazz) {
        try {
            return Optional.of(clazz.cast(this.variableValues));
        } catch (ClassCastException e) {
            System.err.println("Failed to cast value to " + clazz.getName());
            return Optional.empty();
        }
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(className);
        sb.append(",");
        sb.append(methodName);
        sb.append(",");
        sb.append(condition);
        sb.append(",");
        sb.append(pathTaken);
        sb.append(",");
        sb.append(variableNames);
        sb.append(",");
        sb.append(variableValues);

        return sb.toString();
    }
}