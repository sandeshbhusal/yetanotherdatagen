package edu.boisestate.datagen.instrumenters;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.BinaryExpr.Operator;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import edu.boisestate.datagen.reporting.Record;

public class IfStatementInstrumenter extends VoidVisitorAdapter<Void> implements Instrumenter {
    private String currentClass = "";
    private String currentMethod = "";

    private final InstrumentationMode mode;
    private final HashMap<String, List<Record>> recordedValues;

    public IfStatementInstrumenter(InstrumentationMode mode, HashMap<String, List<Record>> recordedValues) {
        this.mode = mode;
        this.recordedValues = recordedValues;
    }

    @Override
    public void visit(ClassOrInterfaceDeclaration def, Void arg) {
        this.currentClass = def.getNameAsString();
        super.visit(def, arg);
        this.currentClass = "";
    }

    @Override
    public void visit(MethodDeclaration def, Void arg) {
        this.currentMethod = def.getNameAsString();
        super.visit(def, arg);
        this.currentMethod = "";
    }

    @Override
    public void visit(IfStmt ifStatementNode, Void arg) {
        // Modify the if statement block such that it calls the augmentation method.
        SimpleNameCollector snc = new SimpleNameCollector();
        ifStatementNode.getCondition().accept(snc, null);

        // if there are no variables, then we don't need to instrument
        if (snc.getNames().size() == 0) {
            return;
        }

        // Ensure neither the true nor false branch has a return statement
        ContainsReturnInstrumenter cri = new ContainsReturnInstrumenter();
        Statement thenStatement = ifStatementNode.getThenStmt();
        if (thenStatement instanceof ReturnStmt) {
            return;
        }

        // We are sure it;s a block statement
        thenStatement.asBlockStmt().accept(cri, null);
        if (cri.containsReturn) {
            return;
        }

        Statement elseStmt = ifStatementNode.getElseStmt().orElse(null);
        if (elseStmt != null) {
            if (elseStmt instanceof ReturnStmt) {
                return;
            }

            // We are sure it;s a block statement
            elseStmt.asBlockStmt().accept(cri, null);
            if (cri.containsReturn) {
                return;
            }
        }

        // Now we are sure there are no returns in the if statement or the else
        // statement
        // or body. We can proceed with instrumentation / augmentation.

        if (mode == InstrumentationMode.AUGMENTATION) {
            this.augmentIfStatement(ifStatementNode, snc);
        }

        if (mode == InstrumentationMode.INSTRUMENTATION) {
            this.instrumentIfStatement(ifStatementNode, snc);
        }
    }

    private void augmentIfStatement(IfStmt ifStatementNode, SimpleNameCollector snc) {
        // Get the variable names involved in the condition
        String[] variables = snc.getNames().toArray(String[]::new);
        String expression = ifStatementNode.getCondition().toString();

        ArrayList<BinaryExpr> expressions = new ArrayList<>();

        for (String variable : variables) {
            // Lookup the values this variable has assumed in this context.
            // The context is built with class -> method -> condition -> variable name ->
            // true/false.
            // We will generate binary expressions for each of the values and negate
            // the branch expressions so that we can generate more data.
            Record recordTrueKeyForVariable = new Record(currentClass, currentMethod, expression, variable, true);
            Record recordFalseKeyForVariable = new Record(currentClass, currentMethod, expression, variable, false);

            List<Record> truthyValues = recordedValues.get(recordTrueKeyForVariable.toString());
            List<Record> falsyValues = recordedValues.get(recordFalseKeyForVariable.toString());

            for (Record record : truthyValues) {
                // Add the variable to the true and false maps
                BinaryExpr trueExpr = new BinaryExpr();
                trueExpr.setLeft(new NameExpr(variable));
                trueExpr.setOperator(Operator.NOT_EQUALS);

                Integer value = record.getValue(Integer.class).orElse(null);
                if (value != null) {
                    trueExpr.setRight(new IntegerLiteralExpr(value.toString()));
                    expressions.add(trueExpr);
                }
            }

            for (Record record : falsyValues) {
                // Add the variable to the true and false maps
                BinaryExpr falseExpr = new BinaryExpr();
                falseExpr.setLeft(new NameExpr(variable));
                falseExpr.setOperator(Operator.NOT_EQUALS);

                Integer value = record.getValue(Integer.class).orElse(null);
                if (value != null) {
                    falseExpr.setRight(new IntegerLiteralExpr(value.toString()));
                    expressions.add(falseExpr);
                }

            }
        }

        if (expressions.size() > 0) {
            // Stitch together the expressions with a logical AND.
            BinaryExpr andExpr = new BinaryExpr();
            andExpr.setLeft(expressions.get(0));
            andExpr.setOperator(Operator.AND);
            for (int i = 1; i < expressions.size(); i++) {
                andExpr.setRight(expressions.get(i));
            }

            // Add the original if statement condition to the start, and the andExpr to the
            // end
            // to make a new binary expression on the if statement condition.
            BinaryExpr newExpr = new BinaryExpr();
            newExpr.setLeft(ifStatementNode.getCondition());
            newExpr.setOperator(Operator.AND);
            newExpr.setRight(andExpr);

            ifStatementNode = ifStatementNode.setCondition(newExpr);
        }
    }

    private void instrumentIfStatement(IfStmt ifStatementNode, SimpleNameCollector snc) {
        // Collect variable names and values
        // Build method call for `if` block
        MethodCallExpr ifMethodCall = createMethodCallExpr(ifStatementNode.getCondition().toString(), true,
                snc.getNames().toArray(String[]::new));

        // Build method call for `else` block
        MethodCallExpr elseMethodCall = createMethodCallExpr(ifStatementNode.getCondition().toString(), false,
                snc.getNames().toArray(String[]::new));

        // Add instrumentation to the `if` block. If it's not a block statement, wrap it
        // in a block statement.
        Statement ifBlock = ifStatementNode.getThenStmt();
        if (!(ifBlock instanceof BlockStmt)) {
            BlockStmt ifBlockStmt = new BlockStmt();
            ifBlockStmt = ifBlockStmt.addStatement(ifBlock);
            ifStatementNode.setThenStmt(ifBlockStmt);
            ifBlock = ifBlockStmt;
        }

        ifBlock = ifBlock.asBlockStmt().addStatement(0, ifMethodCall);

        // Add instrumentation to the `else` block if present, and if it is a block
        // statement
        Statement elseBlock = ifStatementNode.getElseStmt().orElse(null);
        if (elseBlock != null) {
            if (!(elseBlock instanceof BlockStmt)) {
                BlockStmt elseBlockStmt = new BlockStmt();
                elseBlockStmt = elseBlockStmt.addStatement(elseBlock);
                ifStatementNode.setElseStmt(elseBlockStmt);
                elseBlock = elseBlockStmt;
            }
            elseBlock = elseBlock.asBlockStmt().addStatement(0, elseMethodCall);
        }
    }

    private MethodCallExpr createMethodCallExpr(String condition, boolean pathTaken, String[] variableNames) {
        MethodCallExpr methodCallExpr = new MethodCallExpr();

        methodCallExpr.setScope(new NameExpr("Report"));
        methodCallExpr.setName("reportDataPoint");

        methodCallExpr.addArgument(new StringLiteralExpr(currentClass));
        methodCallExpr.addArgument(new StringLiteralExpr(currentMethod));
        methodCallExpr.addArgument(new StringLiteralExpr(condition));
        methodCallExpr.addArgument(new BooleanLiteralExpr(pathTaken));

        if (variableNames != null)
            for (String variableName : variableNames) {
                // For variable named "a", add two arguments - "a" and a.
                methodCallExpr.addArgument(new StringLiteralExpr(variableName));
                methodCallExpr.addArgument(new NameExpr(variableName));
            }

        return methodCallExpr;
    }

    public static String generateKeyForMap(String className, String methodName, String condition, boolean pathTaken) {
        StringBuilder sb = new StringBuilder();

        sb.append(className);
        sb.append(methodName);
        sb.append(condition);
        sb.append(pathTaken);
        return sb.toString();
    }

    @Override
    public void instrument(CompilationUnit cu) {
        cu.accept(this, null);
    }
}
