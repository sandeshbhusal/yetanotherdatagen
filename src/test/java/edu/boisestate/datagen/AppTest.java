package edu.boisestate.datagen;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
import edu.boisestate.datagen.instrumenters.InstrumentationMode;

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
        cc.instrument(cu);
        System.err.println(cc);
    }
}
