package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class IfStatement extends VoidVisitorAdapter<Void> {
    private String currentClass = "";
    private String currentMethod = "";

    public IfStatement(String currentClass, String currentMethod) {
        this.currentClass = currentClass;
        this.currentMethod = currentMethod;
    }

    @Override
    public void visit(com.github.javaparser.ast.stmt.IfStmt n, Void arg) {
        // Modify the if statement block such that it calls the augmentation method.
        SimpleNameCollector snc = new SimpleNameCollector();
        n.getCondition().accept(snc, null);
        System.out.println(snc.getNames());
    }
}
