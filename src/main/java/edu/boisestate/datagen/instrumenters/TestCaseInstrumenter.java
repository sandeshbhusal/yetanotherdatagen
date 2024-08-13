package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class TestCaseInstrumenter extends VoidVisitorAdapter<Void> implements Instrumenter {

    @Override
    public void instrument(CompilationUnit cu) {
    }
}
