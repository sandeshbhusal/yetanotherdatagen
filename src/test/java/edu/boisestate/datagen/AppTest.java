package edu.boisestate.datagen;

import org.junit.Test;
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

    } 
}
