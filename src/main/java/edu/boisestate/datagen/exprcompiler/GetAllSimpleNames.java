package edu.boisestate.datagen.exprcompiler;

import java.util.HashSet;

import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class GetAllSimpleNames extends VoidVisitorAdapter<Void> {

    private HashSet<String> variableNames;

    public GetAllSimpleNames() {
        this.variableNames = new HashSet<>();
    }

    @Override
    public void visit(SimpleName name, Void arg) {
        variableNames.add(name.toString());
    }

    public HashSet<String> getAllVars() {
        return this.variableNames;
    }
}
