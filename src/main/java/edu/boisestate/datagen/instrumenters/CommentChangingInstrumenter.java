package edu.boisestate.datagen.instrumenters;

import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class CommentChangingInstrumenter extends VoidVisitorAdapter<Void> implements Instrumenter {
    private InstrumentationMode mode;

    @Override
    public void visit(BlockStmt block, Void arg) {
        NodeList<Statement> statements = new NodeList<>();
    
        for (Statement stmt : block.getStatements()) {
            stmt.accept(this, null); 
            statements.add(stmt);
        }
    
        NodeList<Statement> modifiedStatements;
        if (this.mode == InstrumentationMode.INSTRUMENTATION) {
            modifiedStatements = convertInstrumentationStatements(statements);
            modifiedStatements = replaceGuardsWithReportingCode(modifiedStatements);
        } else {
            modifiedStatements = recursivelyGenerateGuards(statements);
        }
    
        modifiedStatements = dropAllEmptyStatements(modifiedStatements);
        
        // Set modified statements back to the block
        block.setStatements(modifiedStatements);
    }

    public CommentChangingInstrumenter(InstrumentationMode mode) {
        this.mode = mode;
    }

    public NodeList<Statement> dropAllEmptyStatements(NodeList<Statement> statements) {
        NodeList<Statement> rval = new NodeList<>();
        for (Statement statement : statements) {
            if (statement instanceof EmptyStmt) {
                // Skip this statement.
                continue;
            }
            rval.add(statement);
        }
        return rval;
    }

    // Replace all guard_start statements with Report.datagen_guard_instrument
    // calls.
    public NodeList<Statement> replaceGuardsWithReportingCode(NodeList<Statement> statements) {
        NodeList<Statement> rval = new NodeList<>();
        for (Statement statement : statements) {
            if (statement.getComment().isPresent()
                    && statement.getComment().get().toString().contains("datagen_guard_start")) {
                ArrayList<String> commentContents = new ArrayList<>(
                        Arrays.asList(StringUtils.chomp(statement.getComment().get().asString()).split(" ")));

                Iterator<String> iter = commentContents.iterator();
                iter.next(); // Skip the datagen_guard_start.
                iter.next();

                // This is the start of a guard block.
                String guardId = iter.next();

                System.out.println("Found guard statement with ID: " + guardId);

                // Replace that statement with a reporting call.
                MethodCallExpr guardInstrumentationMethodCall = createMethodCallExpr(guardId,
                        iter);
                rval.add(new ExpressionStmt(guardInstrumentationMethodCall));
            } else {
                rval.add(statement);
            }
        }
        return rval;
    }

    // Convert datagen_instrument statements to method invocations.
    public NodeList<Statement> convertInstrumentationStatements(NodeList<Statement> statements) {
        NodeList<Statement> rval = new NodeList<>();
        for (Statement statement : statements) {
            // Check if this statement is a EmptyStmt and contains a comment
            // with the datagen_instrument command.
            if (!(statement instanceof EmptyStmt && statement.getComment().isPresent())) {
                rval.add(statement);
                continue;
            }

            String comment = statement.getComment().get().toString();

            if (comment.contains("datagen_instrument")) {
                ArrayList<String> commentContents = new ArrayList<>(
                        Arrays.asList(StringUtils.chomp(comment).split(" ")));

                MethodCallExpr methodCall = new MethodCallExpr();
                methodCall.setScope(new NameExpr("Report"));
                methodCall.setName(new SimpleName("datagen_instrument"));

                Iterator<String> iter = commentContents.iterator();
                // Skip the first key, it's datagen_instrument.
                iter.next();

                // Get the instrumentation ID.
                if (iter.hasNext()) {
                    String instrumentationId = iter.next();
                    methodCall.addArgument(new StringLiteralExpr(instrumentationId));

                    while (iter.hasNext()) {
                        String variableName = iter.next();
                        methodCall.addArgument(new StringLiteralExpr(variableName));
                        methodCall.addArgument(new NameExpr(variableName));
                    }

                    // Replace this statement with our generated method call.
                    rval.add(new ExpressionStmt().setExpression(methodCall));
                } else {
                    throw new IllegalArgumentException(
                            "No instrumentation ID found for comment: " + statement.toString());
                }
            } else {
                // Add the statement verbatim. This might be a guard statement, we will
                // handle those later.
                rval.add(statement);
            }
        }

        return rval;
    }

    // Recursively analyze a list of statements, and generate guard "if" statements
    public NodeList<Statement> recursivelyGenerateGuards(NodeList<Statement> statements) {
        NodeList<Statement> rval = new NodeList<>();
        int i = 0;

        while (i < statements.size()) {
            Statement statement = statements.get(i);

            if (statement.getComment().isPresent()
                    && statement.getComment().get().toString().contains("datagen_guard_start")) {
                ArrayList<String> commentContents = new ArrayList<>(
                        Arrays.asList(StringUtils.chomp(statement.getComment().get().asString()).split(" ")));

                Iterator<String> iter = commentContents.iterator();
                iter.next();
                iter.next();
                // This is the start of a guard block.
                String guardId = iter.next();

                System.out.println("Found guard statement with ID: " + guardId);

                // Collect all statements inside this guard block.
                NodeList<Statement> intermediate = new NodeList<>();
                i++; // Move to the statement after the guard start.

                while (i < statements.size()) {
                    Statement innerStatement = statements.get(i);

                    if (innerStatement.getComment().isPresent() &&
                            innerStatement.getComment().get().toString().contains("datagen_guard_end " + guardId)) {
                        System.out.println("Found closing guard for guard " + guardId);
                        break; // Exit the loop when the closing guard is found.
                    } else {
                        intermediate.add(innerStatement);
                    }
                    i++;
                }

                // Recursively resolve nested guards.
                NodeList<Statement> guardedStatements = recursivelyGenerateGuards(intermediate);

                // Wrap the guarded statements in an IfStmt.
                IfStmt wrappingIfStatement = new IfStmt();
                BlockStmt guardedThen = new BlockStmt();
                guardedThen.setStatements(guardedStatements);
                wrappingIfStatement.setThenStmt(guardedThen);
                wrappingIfStatement.setCondition(new BooleanLiteralExpr(true));

                rval.add(wrappingIfStatement);
            } else {
                // If not a guard start, add the statement as is.
                rval.add(statement);
            }

            i++;
        }

        return rval;
    }

    public MethodCallExpr createMethodCallExpr(String guardId, Iterator<String> args) {
        MethodCallExpr methodCallExpr = new MethodCallExpr();

        methodCallExpr.setScope(new NameExpr("Report"));
        methodCallExpr.setName(new SimpleName("datagen_guard_instrument"));

        methodCallExpr.addArgument(new StringLiteralExpr(guardId));

        if (args != null) {
            while (args.hasNext()) {
                String arg = args.next();
                // For variable named "a", add two arguments - "a" and a.
                methodCallExpr.addArgument(new StringLiteralExpr(arg));
                methodCallExpr.addArgument(new NameExpr(arg));
            }
        }

        return methodCallExpr;
    }

    @Override
    public void instrument(CompilationUnit cu) {
        cu.accept(this, null);
    }
}
