package edu.boisestate.datagen.instrumenters;

import java.util.HashSet;

import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class SimpleNameCollector extends VoidVisitorAdapter<Void> {
    private HashSet<String> names = new HashSet<String>();

    @Override
    public void visit(com.github.javaparser.ast.expr.SimpleName n, Void arg) {
        names.add(n.getIdentifier());
    }

    public HashSet<String> getNames() {
        return names;
    }
}
