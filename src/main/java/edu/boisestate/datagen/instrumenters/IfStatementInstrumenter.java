package edu.boisestate.datagen.instrumenters;

import java.util.ArrayList;
import java.util.HashMap;

import org.tinylog.Logger;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import edu.boisestate.datagen.reporting.Record;
import edu.boisestate.datagen.server.Cache;

public class IfStatementInstrumenter extends VoidVisitorAdapter<Void> implements Instrumenter {
    private String currentClass = "";
    private String currentMethod = "";

    private final InstrumentationMode mode;

    public IfStatementInstrumenter(InstrumentationMode mode) {
        this.mode = mode;
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
        // Get the variables in the condition
        SimpleNameCollector snc = new SimpleNameCollector();
        ifStatementNode.getCondition().accept(snc, null);

        // if there are no variables, then we don't need to instrument if the condition does not start with "true"
        if (snc.getNames().size() == 0 && !ifStatementNode.getCondition().toString().startsWith("true")) {
            Logger.debug("No variables found in condition of if statement. Skipping instrumentation.");
            return;
        }

        // Ensure neither the true nor false branch has a return statement
        ContainsReturnInstrumenter cri = new ContainsReturnInstrumenter();
        Statement thenStatement = ifStatementNode.getThenStmt();
        if (thenStatement instanceof ReturnStmt) {
            Logger.debug("Found a return statement in the then branch of the if statement. Skipping instrumentation.");
            return;
        }

        // If it's not a return statement, it could be a block or some other statement.
        // If block, it might contain a return statement.
        thenStatement.accept(cri, null);
        if (cri.containsReturn) {
            Logger.debug("Found a return statement in the then branch of the if statement. Skipping instrumentation.");
            return;
        }

        Statement elseStmt = ifStatementNode.getElseStmt().orElse(null);
        if (elseStmt != null) {
            if (elseStmt instanceof ReturnStmt) {
                Logger.debug("Found a return statement in the else branch of the if statement. Skipping instrumentation.");
                return;
            }
            
            // If it's not a return statement, it could be a block or some other statement.
            // If block, it might contain a return statement.
            elseStmt.accept(cri, null);
            if (cri.containsReturn) {
                Logger.debug("Found a return statement in the else branch of the if statement. Skipping instrumentation.");
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
        // If the condition of the if statement begins with a "true", then we don't need to augment that
        // statement. We will simply continue to traverse the children in the then and else branches, and
        // try to augment this statement.
        // This is basically how it works:
        // TODO: add comments and example.


        if (ifStatementNode.getCondition().toString().startsWith("true")) {
            Logger.debug("Found a wrapping if statement, traversing into children.");
            ifStatementNode.getThenStmt().accept(this, null);
            ifStatementNode.getElseStmt().ifPresent(elseStmt -> elseStmt.accept(this, null));
            return;
        }

        // Get the variable names involved in the condition
        String[] variables = snc.getNames().toArray(String[]::new);
        String expression = ifStatementNode.getCondition().toString();
        Logger.debug("Found a candidate if statement with condition: " + expression);

        // Print out the cached values for each variable.
        Cache cache = Cache.getInstance();
        ArrayList<BinaryExpr> expressions = new ArrayList<>();
        for (String variable : variables) {
            ArrayList<Record> trueValues = cache.getDataPointsForAVariable(currentClass, currentMethod, expression,
                    true, variable);
            ArrayList<Record> falseValues = cache.getDataPointsForAVariable(currentClass, currentMethod, expression,
                    false, variable);

            // Generate binary expressions for each value and this variable.
            trueValues.addAll(falseValues);

            for (Record record : trueValues) {
                BinaryExpr expr = new BinaryExpr();
                expr.setLeft(new NameExpr(variable));
                Integer value = record.getValue(Integer.class).orElseThrow();
                expr.setRight(new IntegerLiteralExpr(String.valueOf(value)));

                expr.setOperator(BinaryExpr.Operator.NOT_EQUALS);
                expressions.add(expr);
            }
        }

        // Dedup
        HashMap<String, BinaryExpr> deduped = new HashMap<>();
        for (BinaryExpr expr : expressions) {
            deduped.put(expr.toString(), expr);
        }

        Logger.debug("Original variable values length: {} and deduped length: {}", expressions.size(), deduped.size());

        expressions.clear();
        expressions.addAll(deduped.values());

        // Get the wrapping "if" statement for this if statement node.
        Node wrappingIfStatement = ifStatementNode.getParentNode().orElse(null);
        if (wrappingIfStatement == null) {
            throw new RuntimeException("Wrapping if statement is null for if statement node: " + ifStatementNode);
        }
        
        if (!(wrappingIfStatement instanceof IfStmt)
                || !(((IfStmt) wrappingIfStatement).getCondition().toString().startsWith("true"))) {
            
            // Print out this statement.
            System.err.println("------ Start of error ------");
            System.out.println(ifStatementNode.toString());
            // Print out the class of the wrapping if statement.
            System.err.println("Expected IfStmt, got " + wrappingIfStatement.getClass().getName());

            // Print out the compilation unit also.
            System.err.println("------ End of error ------");

            // We are doing something wrong here.
            throw new RuntimeException(
                    "Wrapping if statement is not an if statement, or is not wrapped with a 'true' expression.");
        }

        // If there is no augmentation to be done (at the start, we don't have data points).
        // We can just return.
        if (expressions.size() == 0) {
            Logger.debug("No data points found for augmentation. Skipping augmenting the branches.");
            return;
        }

        // Now that the wrapping if statement is found, add all the binary expressions,
        // starting with "true" as the starting of the expression in the wrapping if statement.
        // E.g. for
        // if (true) if (a < b)
        // we will make it:
        // if (true && a != 1 && b != 2) if (a < b)
        
        BinaryExpr innerExpr = new BinaryExpr();
        innerExpr.setLeft(new BooleanLiteralExpr(true));
        innerExpr.setOperator(BinaryExpr.Operator.AND);
        for (BinaryExpr expr : expressions) {
            innerExpr.setRight(expr);
            innerExpr.setLeft(innerExpr.clone());
            innerExpr.setOperator(BinaryExpr.Operator.AND);
        }
        innerExpr.setRight(new BooleanLiteralExpr(true));

        // Set the new condition to the wrapping if statement.
        // SAFETY: This cast will always work.
        IfStmt wrapper = (IfStmt) wrappingIfStatement;
        wrapper.setCondition(innerExpr);
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
