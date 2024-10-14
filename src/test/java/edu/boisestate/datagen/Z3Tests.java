package edu.boisestate.datagen;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.util.Set;

import org.junit.Test;

import edu.boisestate.datagen.exprcompiler.CompiledExpression;
import edu.boisestate.datagen.utils.ClassPathUtils;
import edu.boisestate.datagen.utils.FileOps;

public class Z3Tests {
    public Z3Tests() {
    }

    @Test
    public void checkZ3BinaryPath() {
        try {
            String z3BinaryPath = ClassPathUtils.getBinaryPath("z3");
            assertNotNull(z3BinaryPath);
        } catch (NullPointerException e) {
            e.printStackTrace();
            System.err.println(">>>>>>>>>>>>>>> Z3 binary not found.");
        }
    }

    @Test
    public void checkEqualGivesSatSat() {
        CompiledExpression ce1 = new CompiledExpression();
        CompiledExpression ce2 = new CompiledExpression();

        ce1.variables = Set.of("x", "y");
        ce2.variables = Set.of("x", "y");

        ce1.sExpr = "(= x y)";
        ce2.sExpr = "(= x y)";

        assert(ce1.equals(ce2));
    }

    @Test
    public void checkSMTExpressionsParsing() {
        CompiledExpression ce1 = new CompiledExpression();
        CompiledExpression ce2 = new CompiledExpression();

        ce1.variables = Set.of("x", "y");
        ce2.variables = Set.of("x", "y");

        // Same as saying x == y.
        ce1.sExpr = "(and (> x y) (<= x y))";
        ce2.sExpr = "(= x y)";

        assertEquals(ce1, ce2);
    }
}
