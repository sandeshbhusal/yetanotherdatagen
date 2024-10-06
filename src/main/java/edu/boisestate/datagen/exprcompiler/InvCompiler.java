package edu.boisestate.datagen.exprcompiler;

import java.util.HashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;

public class InvCompiler {
    public static class CompiledExpression {
        public HashSet<String> variables;
        public String sExpr;
    }

    public static String preProcessExpr(String expr) {
        // A couple of steps need to be done on the expr before we can
        // begin to parse it.
        // They are:
        // 1. Remove all newlines, spaces, around the expr.
        // 2. Convert dig mod exprs to daikon mod exprs (see below).

        expr = StringUtils.chomp(expr.trim());

        Pattern pat = Pattern.compile(
            "(.+)\\s*===\\s*(.+)\\s*\\(mod\\s*(.+)\\)"
        );
        Matcher matcher = pat.matcher(expr);

        if (matcher.matches()) {
            String lhs = matcher.group(1).trim();
            String rhs = matcher.group(3).trim();
            String res = matcher.group(2).trim();

            // WHY JAVA WHY ?!
            expr = String.format("%s %% %s == %s", lhs, rhs, res);
        }

        // Dig represents power as **, like x ** 2 means x squared.
        // Since we are using Javaparser, we need to convert it to a format
        // that Javaparser understands.
        //
        // Assuming our invariant exprs do not use XOR, we can use the ^ symbol for
        // now, and convert it inside JavaExpr2SExpr.

        expr = expr.replaceAll("\\*\\*", "^");

        return expr;
    }


}
