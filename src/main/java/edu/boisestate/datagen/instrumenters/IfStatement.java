package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.ast.CompilationUnit;

public class IfStatement extends VoidVisitorAdapter<Void> {
    private String currentClass = "";
    private String currentMethod = "";

    public IfStatement(String currentClass, String currentMethod) {
        this.currentClass = currentClass;
        this.currentMethod = currentMethod;
    }

    @Override
    public void visit(com.github.javaparser.ast.stmt.IfStmt n, Void arg) {
        // System.out.println("Visiting if statement");
        // CompilationUnit cu = new CompilationUnit(currentClass, currentMethod);
        // cu.findAll(IfStatement).stream().forEach(ifStmt -> System.out.println(ifStmt.toString()));
    }
}
