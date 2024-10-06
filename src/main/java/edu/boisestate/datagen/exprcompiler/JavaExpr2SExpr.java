package edu.boisestate.datagen.exprcompiler;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

/* JavaExpr2SExpr is the main converter that converts a given java
 * expression to a s-expression. The s-expression is a simplified prefix
 * notation of the java expression. The s-expression is used to generate
 * smt expressions for SMT solvers like z3.
 */
public class JavaExpr2SExpr extends VoidVisitorAdapter<Void> {

    StringBuilder sb;

    @Override
    public void visit(BinaryExpr n, Void arg) {
        // Special case: if BinaryExpr is ==, we cannot use '==' since
        // SMT format is '=' only.

        sb.append("(");

        switch (n.getOperator()) {
            case PLUS:
                sb.append("+");
                break;
            case MINUS:
                sb.append("-");
                break;
            case MULTIPLY:
                sb.append("*");
                break;
            case DIVIDE:
                sb.append("/");
                break;
            case REMAINDER:
                sb.append("%");
                break;
            case LESS:
                sb.append("<");
                break;
            case GREATER:
                sb.append(">");
                break;
            case LESS_EQUALS:
                sb.append("<=");
                break;
            case GREATER_EQUALS:
                sb.append(">=");
                break;
            case NOT_EQUALS:
                sb.append("!=");
                break;
            case EQUALS:
                sb.append("=");
                break;
            case XOR:
                sb.append("(pow ");
                n.getLeft().accept(this, arg);
                sb.append(" ");
                n.getRight().accept(this, arg);
                sb.append(")");
                return;

            default:
                throw new IllegalArgumentException("Invalid operator in expr: " + n.getOperator());
        }

        sb.append(" ");
        n.getLeft().accept(this, arg);
        sb.append(" ");
        n.getRight().accept(this, arg);
        sb.append(")");
    }

    @Override
    public void visit(UnaryExpr n, Void arg) {
        sb.append("(");
        sb.append(n.getOperator());
        sb.append(" ");
        n.getExpression().accept(this, arg);
        sb.append(")");
    }

    @Override
    public void visit(SimpleName n, Void arg) {
        sb.append(n.getIdentifier());
    }

    @Override
    public void visit(IntegerLiteralExpr n, Void arg) {
        sb.append(n.getValue());
    }

    public String getExpr() {
        return sb.toString().trim();
    }

    public JavaExpr2SExpr() {
        this.sb = new StringBuilder();
    }
}
