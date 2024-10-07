package edu.boisestate.datagen;

import static org.junit.Assert.assertEquals;

import java.io.StringReader;
import java.util.HashSet;

import org.junit.Test;

import com.github.javaparser.ast.expr.Expression;

import edu.boisestate.datagen.exprcompiler.GetAllSimpleNames;
import edu.boisestate.datagen.exprcompiler.InvCompiler;
import edu.boisestate.datagen.exprcompiler.JavaExpr2SExpr;

public class TestCompiler {

    @Test
    public void testPreprocess() throws Exception {
        // Check if the transformations from dig to daikon mod invariants are done.
        // Dig generates invariants like "expr1 === expr2 (mod expr3)" but we want
        // "expr1 % expr3 == expr2"

        String input = "  x1 === x2 (mod x3)\n";
        String expected = "((x1) % (x3)) == x2";
        assertEquals(expected, InvCompiler.preProcessExpr(input));
    }

    @Test
    public void test_s_expr_conversions() throws Exception {
        // Check if our s-expr conversions are working fine or not.
        String expr = "x1 + x2*2 == x3+5";

        Expression exp = InvCompiler.generateJavaExpressionFromString(expr);
        JavaExpr2SExpr j2s = new JavaExpr2SExpr();
        exp.accept(j2s, null);

        String sExpr = j2s.getExpr();
        assertEquals(sExpr, "(= (+ x1 (* x2 2)) (+ x3 5))");
    }

    @Test
    public void test_expr_conversions_hammer() throws Exception {
        // This test runs a bunch of possible scenarios on the converter
        // to see if any case fails. We do not care about the output here,
        // just trying to see if something breaks.

        String[] candidateExprs = {
            "x1",
            "x1 + x2",
            "x1 * 2",
            "x1 ** 3",
            "x1 / x2",
            "max(x1, x2)",
            "(x1 + x2) - x3",
        };

        String[] candidateOperators = {
            "+",
            "-",
            "*",
            "/",
            "%",
            "==",
            "!=",
            "<",
            "<=",
            ">",
            ">=",
        };

        for (String exp1 : candidateExprs) {
            for (String exp2 : candidateExprs) {
                for (String op : candidateOperators) {
                    // Generate a infix expression.
                    String expression = String.format(
                        "%s %s %s",
                        exp1,
                        op,
                        exp2
                    );

                    Expression exp =
                        InvCompiler.generateJavaExpressionFromString(
                            expression
                        );
                    JavaExpr2SExpr j2s = new JavaExpr2SExpr();
                    exp.accept(j2s, null);
                }
            }
        }
    }

    @Test
    public void test_get_vars() throws Exception {
        HashSet<String> checkvars = new HashSet<>();
        checkvars.add("x1");
        checkvars.add("x2");
        checkvars.add("x3");

        String expr = "x1 + x2*2 == x3+5";

        Expression exp = InvCompiler.generateJavaExpressionFromString(expr);
        GetAllSimpleNames gsn = new GetAllSimpleNames();
        exp.accept(gsn, null);

        HashSet<String> parsedvars = gsn.getAllVars();
        assert (parsedvars.size() == checkvars.size());
        for (String checkvar : checkvars) {
            assert (parsedvars.contains(checkvar));
        }
    }

    @Test
    public void test_dig_expr_conversions() throws Exception {
        StringBuilder digFileContents = new StringBuilder();
        digFileContents.append("vtrace1 (4 invs): \n");
        digFileContents.append("1. a <= 0\n");
        digFileContents.append("2. -b <= 0\n");
        digFileContents.append("3. a === 0 (mod 6)\n");
        digFileContents.append("4. a - b === 0 (mod 2)");

        InvCompiler compiler = new InvCompiler();
        compiler
            .digFileToInvariantsConjunction(
                new StringReader(digFileContents.toString())
            )
            .toString();
    }

    @Test
    public void test_daikon_expr_conversions() throws Exception {
        StringBuilder daikonFileContents = new StringBuilder();
        daikonFileContents.append("Faker.fakemethod(int, int):::DATAGEN\n");
        daikonFileContents.append("a >= b\n");
        daikonFileContents.append("b one of { -2700, -606, 0 }\n");
        daikonFileContents.append("a % b == 2\n");
        daikonFileContents.append("Exiting Daikon.");

        InvCompiler compiler = new InvCompiler();
        compiler
            .daikonFileToInvariantsConjunction(
                new StringReader(daikonFileContents.toString())
            )
            .toString();
    }
}
