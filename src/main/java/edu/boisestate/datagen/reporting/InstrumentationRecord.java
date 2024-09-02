package edu.boisestate.datagen.reporting;

import java.util.HashMap;
import java.io.Serializable;

/* A record at a particular point in the instrumentation process */
public class InstrumentationRecord implements Serializable {
    private static final long serialVersionUID = 0x0decaf_43C;

    // A record is simple - it contains the values of different variables,
    // captured at a particular point where it was generated.

    private final String RecordId;
    private HashMap<String, Object> values;
    private RecordType type;

    public static enum RecordType {
        INSTRUMENTATION,
        GUARD
    }

    public InstrumentationRecord(RecordType type,String RecordId, HashMap<String, Object> values) {
        this.RecordId = RecordId;
        this.values = values;
    }

    public String getRecordId() {
        return RecordId;
    }

    public HashMap<String, Object> getValues() {
        return values;
    }

    public RecordType getType() {
        return type;
    }

    // ToString impl.
    @Override
    public String toString() {
        return "Record [RecordId=" + RecordId + ", values=" + values + "]" + " (Type = " + type + ")";
    }
}