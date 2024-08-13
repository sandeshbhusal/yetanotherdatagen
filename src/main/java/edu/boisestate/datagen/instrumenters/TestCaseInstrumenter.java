package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class TestCaseInstrumenter extends VoidVisitorAdapter<Void> implements Instrumenter {
    @Override
    public void visit(MethodDeclaration md, Void aVoid) {
        boolean isTestCase = md.getAnnotations().stream()
                .anyMatch(annotation -> annotation.getName().getIdentifier().equals("Test"));

        System.out.println("# Instrumenting found testcase: \'" + md.getNameAsString() + "\'");

        if (isTestCase) {
            // Continue to traverse this method, because it is a test case that might
            // trigger some data paths.

            // Get method body.
            BlockStmt body = md.getBody().orElse(null);
            if (body == null) {
                // Nothing to do. Maybe abstract method or it is empty.
                return;
            }

            String bodyContent = body.toString();
            if (bodyContent.contains("DataGen.startTestCase")) {
                // This should fix the issue of multiple runs of the same test case.
                // This method already has a call to DataGen.addTestCase().
                // Nothing to do.
                return;
            }

            MethodCallExpr startExpressionStmt = new MethodCallExpr(new NameExpr("Report"), "startTestCase");
            startExpressionStmt.addArgument(new StringLiteralExpr(bodyContent));

            body = body.addStatement(0, new ExpressionStmt(startExpressionStmt));

            body = body.addStatement(body.getStatements().size(), new ExpressionStmt(new MethodCallExpr(new NameExpr("Report"), "endTestCase")));
       }
    }

    @Override
    public void instrument(CompilationUnit cu) {
        cu.accept(this, null);
    }
}
