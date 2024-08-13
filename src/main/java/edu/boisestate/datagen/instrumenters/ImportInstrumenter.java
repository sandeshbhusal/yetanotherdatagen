package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class ImportInstrumenter extends VoidVisitorAdapter<Void> implements Instrumenter {
    @Override
    public void visit(CompilationUnit cu, Void arg) {
        ImportDeclaration importDecl = new ImportDeclaration("edu.boisestate.datagen.reporting", false, true);
        cu = cu.addImport(importDecl);
    }

    @Override
    public void instrument(CompilationUnit cu) {
        visit(cu, null);
    }
}
