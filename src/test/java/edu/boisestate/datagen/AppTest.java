package edu.boisestate.datagen;

import java.util.HashMap;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.IfStatementInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;
import edu.boisestate.datagen.reporting.Record;

/**
 * Unit test for simple App.
 */
public class AppTest {
    /**
     * Rigorous Test :-)
     */
    @Test
    public void checkAugmentedIfBranches() {
        StringBuilder sb = new StringBuilder();
        sb.append("public class Test{");
        sb.append("public static void main(String[] args){");
        sb.append("int a = 0; int b = 1;");
        sb.append("if(a < b){");
        sb.append("System.out.println(\"Hello World\");");
        sb.append("}");
        sb.append("}");
        sb.append("}");

        String source = sb.toString();
        
        Record point1at = new Record("Test", "main", "a < b", "a", true, 1);
        Record point1bt = new Record("Test", "main", "a < b", "b", true, 5);        Record point1af = new Record("Test", "main", "a < b", "a", true, 10);
        Record point1bf = new Record("Test", "main", "a < b", "b", true, 3);
        
        HashMap<String, Record> points = new HashMap<>();
        points.put(point1at.toStringKey(), point1at);
        points.put(point1bt.toStringKey(), point1bt);
        points.put(point1af.toStringKey(), point1af);
        points.put(point1bf.toStringKey(), point1bf);
        
        IfStatementInstrumenter ifInstrumenter = new IfStatementInstrumenter(
                InstrumentationMode.AUGMENTATION, points);

        JavaParser parser = new JavaParser();
        CompilationUnit cu = parser.parse(source).getResult().get();

        ifInstrumenter.instrument(cu);
        System.out.println(cu.toString());
    } 
}
