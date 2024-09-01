package edu.boisestate.datagen.instrumenters;

import java.util.Optional;

import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
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

    @Override
    public void visit(MethodDeclaration md, Void arg) {
        // Get body.
        Optional<BlockStmt> body = md.getBody();
        if (!(body.isPresent() && body.get() instanceof BlockStmt)) {
            return;
        }

        BlockStmt block = (BlockStmt) body.get();
        BlockStmt modified = new BlockStmt();

        NodeList<Statement> statements = new NodeList<Statement>();
        for (Statement stmt : block.getStatements()) {
            statements.add(stmt.clone());
        }
        statements = convertInstrumentationStatements(statements);
        modified.setStatements(recursivelyGenerateGuards(statements));

        // set the new block.
        md.setBody(modified);
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
    
            if (statement.getComment().isPresent() && statement.getComment().get().toString().contains("datagen_guard_start")) {
                // This is the start of a guard block.
                String guardId = statement.getComment().get().toString().split(" ")[1];
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

    @Override
    public void instrument(CompilationUnit cu) {
        cu.accept(this, null);
    }
}
