package edu.boisestate.datagen.instrumenters;

import java.util.ArrayList;

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
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
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

        // if there are no variables, then we don't need to instrument if the condition
        // does not start with "true"
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
                Logger.debug(
                        "Found a return statement in the else branch of the if statement. Skipping instrumentation.");
                return;
            }

            // If it's not a return statement, it could be a block or some other statement.
            // If block, it might contain a return statement.
            elseStmt.accept(cri, null);
            if (cri.containsReturn) {
                Logger.debug(
                        "Found a return statement in the else branch of the if statement. Skipping instrumentation.");
                return;
            }
        }

        // Now we are sure there are no returns in the if statement or the else
        // statement
        // or body. We can proceed with instrumentation / augmentation.
        if (mode == InstrumentationMode.AUGMENTATION) {
            this.augmentIfStatement(ifStatementNode);
        }

        if (mode == InstrumentationMode.INSTRUMENTATION) {
            this.instrumentIfStatement(ifStatementNode, snc);
        }
    }

    private void augmentIfStatement(IfStmt ifStatementNode) {
        // If the condition of the if statement begins with a "true", then we don't need
        // to augment that
        // statement. We will simply continue to traverse the children in the then and
        // else branches, and
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
        String expression = ifStatementNode.getCondition().toString();
        Logger.debug("Found a candidate if statement with condition: " + expression);

        // Print out the cached values for each variable.
        Cache cache = Cache.getInstance();

        // Get all traces that lead to this point.
        ArrayList<Record> traces_true = cache.getDataPointsForPath(currentClass, currentMethod, expression, true);
        ArrayList<Record> traces_false = cache.getDataPointsForPath(currentClass, currentMethod, expression, false);
        ArrayList<Record> traces = new ArrayList<>();
        traces.addAll(traces_true);
        traces.addAll(traces_false);

        // Traverse the traces list, and for each variable-value pair, generate an
        // expression.
        // for e.g. if we have class->method->a<b->{true, false} and the traces look
        // like:
        // {a->1, b->2}, {a->2, b->3}, {a->3, b->4}
        // then we will generate the following expressions:
        // !(a == 1 && b == 2) && !(a == 2 && b == 3) && !(a == 3 && b == 4)
        // One more advantage of this approach is we can generate the csv files to run
        // through
        // DIG tool.

        ArrayList<UnaryExpr> expressions = new ArrayList<>();
        for (Record trace : traces) {
            ArrayList<BinaryExpr> binaryExprs = new ArrayList<>();

            for (String variable : trace.getVariablesInTrace()) {
                BinaryExpr binaryExpr = new BinaryExpr();
                binaryExpr.setLeft(new NameExpr(variable));
                binaryExpr.setRight(
                        new IntegerLiteralExpr(String.valueOf(trace.getValue(variable, Integer.class).orElseThrow())));
                binaryExpr.setOperator(BinaryExpr.Operator.EQUALS);
                binaryExprs.add(binaryExpr);
            }

            if (binaryExprs.size() == 0) {
                // Nothing to do for this path.
                return;
            }

            BinaryExpr combinedExpr = binaryExprs.get(0);
            for (int i = 1; i < binaryExprs.size(); i++) {
                combinedExpr = new BinaryExpr(combinedExpr, binaryExprs.get(i), BinaryExpr.Operator.AND);
            }

            // Enclose the combined expression in parentheses
            EnclosedExpr enclosedExpr = new EnclosedExpr(combinedExpr);

            // Negate the enclosed expression
            UnaryExpr negatedExpr = new UnaryExpr(enclosedExpr, UnaryExpr.Operator.LOGICAL_COMPLEMENT);

            // Add the negated expression to the expressions list
            expressions.add(negatedExpr);
        }

        // Combine all unary expressions with AND, starting with "true"
        BinaryExpr innerExpr = new BinaryExpr();
        innerExpr.setLeft(new BooleanLiteralExpr(true));
        innerExpr.setOperator(BinaryExpr.Operator.AND);

        for (UnaryExpr expr : expressions) {
            innerExpr.setRight(expr);
            innerExpr.setOperator(BinaryExpr.Operator.AND);
            innerExpr.setLeft(innerExpr.clone());
        }
        
        innerExpr.setOperator(BinaryExpr.Operator.AND);
        innerExpr.setRight(new BooleanLiteralExpr(true));
        // Print the inner expression
        System.out.println("Inner expression: " + innerExpr);

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

        // If there is no augmentation to be done (at the start, we don't have data
        // points).
        // We can just return.
        if (expressions.size() == 0) {
            Logger.debug("No data points found for augmentation. Skipping augmenting the branches.");
            return;
        }

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
