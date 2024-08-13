package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.CompilationUnit;

public interface Instrumenter {
    void instrument(CompilationUnit cu);
}
