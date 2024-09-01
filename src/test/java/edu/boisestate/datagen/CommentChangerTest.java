package edu.boisestate.datagen;
import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;

import edu.boisestate.datagen.instrumenters.CommentChangingInstrumenter;
public class CommentChangerTest {
    @Test
    public void testCommentChanger() {
        String code = "public class Test {\n" +
                "    public void test() {\n" +
                "        // datagen_instrument a b c\n" +
                "        int a = 1;\n" +
                "        int b = 2;\n" +
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
