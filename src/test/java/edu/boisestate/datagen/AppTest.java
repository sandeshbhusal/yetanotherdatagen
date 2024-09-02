package edu.boisestate.datagen;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

import java.util.HashMap;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.reporting.InstrumentationRecord;

/**
 * Unit test for simple App.
 */
public class AppTest {
    /**
     * Rigorous Test :-)
     */
    @Test
    public void checkAugmentedIfBranches() {
        String code = "import java.io.*;\n" +
                "\n" +
                "public class Input {\n" +
                "    public static boolean intdiv(int a, int b) {\n" +
                "        boolean rval = false;\n" +
                "\n" +
                "        //datagen_instrument entermethod a b\n" +
                "        ;\n" +
                "    \n" +
                "        // datagen_guard_start outerguard a b\n" +
                "        ;\n" +
                "\n" +
                "        if(a < b) {\n" +
                "            //datagen_instrument a_lt_b_true a b\n" +
                "            ;\n" +
                "\n" +
                "            rval = true;\n" +
                "        } else {\n" +
                "            //datagen_instrument a_lt_b_false a b\n" +
                "            ;\n" +
                "\n" +
                "            rval = false;\n" +
                "        }\n" +
                "\n" +
                "        // datagen_guard_end outerguard\n" +
                "        ;\n" +
                "\n" +
                "        return rval;\n" +
                "    }\n" +
                "}";

        CommentChangingInstrumenter cc = new CommentChangingInstrumenter(InstrumentationMode.AUGMENTATION);
        JavaParser parser = new JavaParser();
        CompilationUnit cu = parser.parse(code).getResult().get();
        // cc.instrument(cu);
        System.err.println(cc);
    }

    @Test
    public void checkInstrumentationRecordEquality() {
        InstrumentationRecord record1 = new InstrumentationRecord(InstrumentationRecord.RecordType.INSTRUMENTATION,
                "1", new HashMap<>());
        InstrumentationRecord record2 = new InstrumentationRecord(InstrumentationRecord.RecordType.INSTRUMENTATION,
                "1", new HashMap<>());

        assertEquals(record1, record2);

        // Check same map, but differen types.
        InstrumentationRecord record3 = new InstrumentationRecord(InstrumentationRecord.RecordType.GUARD,
                "1", new HashMap<>());
        assertNotEquals(record1, record3);

        // Check same everything but different records.
        InstrumentationRecord record4 = new InstrumentationRecord(InstrumentationRecord.RecordType.INSTRUMENTATION,
                "2", new HashMap<>());
        assertNotEquals(record1, record4);

        // Check same everything but different values.
        HashMap<String, Object> values = new HashMap<>();
        values.put("a", 1);
        values.put("b", 2);
        values.put("c", 3);
        record4 = new InstrumentationRecord(InstrumentationRecord.RecordType.INSTRUMENTATION,
                "1", values);

        assertNotEquals(record1, record4);

        // Make sure two records with same values are equal.
        HashMap<String, Object> values2 = new HashMap<>();
        values2.put("a", 1);
        values2.put("b", 2);
        values2.put("c", 3);
        InstrumentationRecord record5 = new InstrumentationRecord(InstrumentationRecord.RecordType.INSTRUMENTATION,
                "1", values2);
        assertEquals(record4, record5);
    }
}
