package edu.boisestate.datagen.reporting;

import java.util.HashMap;

/* A record at a particular point in the instrumentation process */
@SuppressWarnings("unused")
public class InstrumentationRecord {
    private static final long serialVersionUID = 0x0decaf_43C;

    // A record is simple - it contains the values of different variables,
    // captured at a particular point where it was generated.

    private final String RecordId;
    private HashMap<String, Object> values;

    public InstrumentationRecord(String RecordId, HashMap<String, Object> values) {
        this.RecordId = RecordId;
        this.values = values;
    }

    public String getRecordId() {
        return RecordId;
    }

    public HashMap<String, Object> getValues() {
        return values;
    }

    // ToString impl.
    @Override
    public String toString() {
        return "Record [RecordId=" + RecordId + ", values=" + values + "]";
    }
}