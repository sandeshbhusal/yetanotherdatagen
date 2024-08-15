package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.ast.Node;

public class Wrapper extends VoidVisitorAdapter<Void> implements Instrumenter {
    private CompilationUnit cu;

    @Override
    public void visit(IfStmt stmt, Void arg) {
        super.visit(stmt, arg);

        // Create a new if statement with the condition always true
        IfStmt newIfStmt = new IfStmt();
        newIfStmt.setCondition(new BooleanLiteralExpr(true));
        
        // Set the original if statement as the then statement of the new if statement
        newIfStmt.setThenStmt(stmt.clone());

        // Replace the old if statement with the new one
        Node parentNode = stmt.getParentNode().orElse(null);
        if (parentNode != null) {
            parentNode.replace(stmt, newIfStmt);
        }
        
        // Print compilation unit after replacing the node
        System.out.println("After replacing node:");
        System.out.println(cu.toString());
    }

    @Override
    public void instrument(CompilationUnit cu) {
        this.cu = cu;
        cu.accept(this, null);
    }
}
