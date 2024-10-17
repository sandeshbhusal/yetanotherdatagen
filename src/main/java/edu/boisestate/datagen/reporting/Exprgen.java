package edu.boisestate.datagen.reporting;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.UnaryExpr;


public class Exprgen {
    public Expression generateBinaryExprFromData(String guardID) {
        List<HashMap<String, Object>> data = Cache.getInstance().get_seen_guard_data(guardID);
        if (data != null) {
            HashSet<UnaryExpr> datapoints_negated = new HashSet<>();
            HashSet<String> dedupset = new HashSet<>(); // For some reason,
                                                        // the same expression is not deduped by hashset.

            // Generate a bunch of Not_equals expressions for each variable,
            // and values.
            for (HashMap<String, Object> trace : data) {
                ArrayList<BinaryExpr> binaryExprs = new ArrayList<>();

                for (String variable : trace.keySet()) {
                    BinaryExpr binaryExpr = new BinaryExpr();
                    binaryExpr.setLeft(new NameExpr(variable));
                    binaryExpr.setRight(
                            new IntegerLiteralExpr(String.valueOf(trace.get(variable))));
                    binaryExpr.setOperator(BinaryExpr.Operator.EQUALS);
                    binaryExprs.add(binaryExpr);
                }

                // Join the binary expressions with "AND"
                BinaryExpr combinedExpr = binaryExprs.get(0);
                for (int j = 1; j < binaryExprs.size(); j++) {
                    combinedExpr = new BinaryExpr(
                            combinedExpr.clone(),
                            binaryExprs.get(j),
                            BinaryExpr.Operator.AND);
                }

                EnclosedExpr enclosedExpr = new EnclosedExpr(combinedExpr);

                // Negate the expression
                UnaryExpr negatedExpr = new UnaryExpr(enclosedExpr, UnaryExpr.Operator.LOGICAL_COMPLEMENT);
                if (!dedupset.contains(negatedExpr.toString())) {
                    dedupset.add(negatedExpr.toString());
                    datapoints_negated.add(negatedExpr);
                }
            }

            // Join all negated exprs with "AND"
            BinaryExpr replacementExpression = new BinaryExpr();
            replacementExpression.setLeft(new BooleanLiteralExpr(true));
            replacementExpression.setOperator(BinaryExpr.Operator.AND);

            for (UnaryExpr expr : datapoints_negated) {
                replacementExpression.setRight(expr);
                replacementExpression.setOperator(BinaryExpr.Operator.AND);
                replacementExpression.setLeft(replacementExpression.clone());
            }

            System.out.println("Replacement expr: " + replacementExpression.toString());
            return replacementExpression;

        } else {
            // return a "true" expression.
            return new BooleanLiteralExpr(true);
        } 
    }
}
