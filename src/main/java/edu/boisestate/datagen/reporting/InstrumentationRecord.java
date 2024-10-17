package edu.boisestate.datagen.reporting;

import java.util.HashMap;
import java.util.Objects;
import java.io.Serializable;

/* A record at a particular point in the instrumentation process */
public class InstrumentationRecord implements Serializable {
    private static final long serialVersionUID = 0x0decaf_43C;

    // A record is simple - it contains the values of different variables,
    // captured at a particular point where it was generated.

    private final String RecordId;
    private HashMap<String, Object> values;
    private RecordType recordType;

    public static enum RecordType {
        INSTRUMENTATION,
        GUARD
    }

    public InstrumentationRecord(RecordType type, String RecordId, HashMap<String, Object> values) {
        this.recordType = type;
        this.RecordId = RecordId;
        this.values = values;
    }

    public String getRecordId() {
        return RecordId;
    }

    public HashMap<String, Object> getValues() {
        return values;
    }

    public RecordType getRecordType() {
        return recordType;
    }

    // ToString impl.
    @Override
    public String toString() {
        return "Record [RecordId=" + RecordId +
                ", values=" + values + "]" +
                " (Type = " + (recordType == RecordType.INSTRUMENTATION ? "INSTRUMENTATION" : "GUARD") + ")";
    }

    // Equality impl.
    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass())
            return false;
        InstrumentationRecord that = (InstrumentationRecord) o;
        if (recordType != that.recordType)
            return false;
        if (!RecordId.equals(that.RecordId))
            return false;

        // If everything matches, compare the variables' set.
        if (!(values.keySet().equals(that.values.keySet())))
            return false;

        // If even the keyset matches, compare the actual values.
        for (String key : values.keySet()) {
            if (!values.get(key).equals(that.values.get(key)))
                return false;
        }

        // Well, everything matches at this point.
        // These records are identical.
        return true;
    }

    @Override
    public int hashCode() {
        return Objects.hash(this.recordType, this.RecordId, this.values);
    }
}