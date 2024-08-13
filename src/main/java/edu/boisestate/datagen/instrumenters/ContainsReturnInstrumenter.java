package edu.boisestate.datagen.instrumenters;

import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class ContainsReturnInstrumenter extends VoidVisitorAdapter<Void> {
    public boolean containsReturn;

    @Override
    public void visit(BlockStmt blockStmt, Void aVoid) {
        this.containsReturn = blockStmt.getStatements().stream().anyMatch(stmt -> stmt instanceof ReturnStmt);
    }

    public static boolean containsReturn(BlockStmt blockStmt) {
        ContainsReturnInstrumenter containsReturn = new ContainsReturnInstrumenter();
        containsReturn.visit(blockStmt, null);

        return containsReturn.containsReturn;
    }
}
