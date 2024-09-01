package edu.boisestate.datagen;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
/**
 * Unit test for simple App.
 */
public class AppTest {
    /**
     * Rigorous Test :-)
     */
    @Test
    public void checkAugmentedIfBranches() {
        String code = "public class Test {\n" +
                "    public void test() {\n" +
                "        // datagen_instrument initpt a b c\n" +
                "        ;\n\n" +
                "        //datagen_guard_start firstguard a b\n" +
                "        ;\n\n" +
                "        int b = 2;\n" +
                "        //datagen_guard_start innerguard b\n" +
                "        ;\n\n" +
                "        int a = 1;\n" +
                "        //datagen_guard_end innerguard\n;\n" +
                "        //datagen_guard_end firstguard\n;\n" +
                "    }\n" +
                "}";

        System.out.println(code);
        CommentChangingInstrumenter cc = new CommentChangingInstrumenter();
        JavaParser parser = new JavaParser();
        CompilationUnit cu = parser.parse(code).getResult().get();
        cc.instrument(cu);

        System.out.println(cu.toString());

    } 
}
