package edu.boisestate.datagen.exprcompiler;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.expr.Expression;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.commons.lang3.StringUtils;

public class InvCompiler {

    /**
     * Preprocesses a string expression to prepare it for parsing by performing several modifications.
     *
     * <p>This method performs two main preprocessing tasks:
     * <ol>
     *   <li>Removes all newlines and leading/trailing spaces from the expression.</li>
     *   <li>Converts "mod" expressions in the form of {@code lhs === rhs (mod divisor)} into
     *   Java-compatible expressions of the form {@code (lhs % divisor) == rhs}.</li>
     *   <li>Replaces the exponentiation operator {@code **} (used by Dig) with {@code ^}, which is handled later in {@code JavaExpr2SExpr}
     *   (assuming {@code ^} is not used for XOR).</li>
     * </ol>
     * This preprocessing is necessary to convert the input into a form that can be parsed correctly using JavaParser.
     * </p>
     *
     * @param expr The string expression to preprocess.
     * @return The preprocessed expression ready for parsing.
     */
    public static String preProcessExpr(String expr) {
        // A couple of steps need to be done on the expr before we can
        // begin to parse it.
        // They are:
        // 1. Remove all newlines, spaces, around the expr.
        // 2. Convert dig mod exprs to daikon mod exprs (see below).

        expr = StringUtils.chomp(expr.trim());

        Pattern pat = Pattern.compile(
            "(.+)\\s*===\\s*(.+)\\s*\\(mod\\s*(.+)\\)"
        );
        Matcher matcher = pat.matcher(expr);

        if (matcher.matches()) {
            String lhs = matcher.group(1).trim();
            String rhs = matcher.group(3).trim();
            String res = matcher.group(2).trim();

            expr = String.format("((%s) %% (%s)) == %s", lhs, rhs, res);
        }

        // Dig represents power as **, like x ** 2 means x squared.
        // Since we are using Javaparser, we need to convert it to a format
        // that Javaparser understands.
        //
        // Assuming our invariant exprs do not use XOR, we can use the ^ symbol for
        // now, and convert it inside JavaExpr2SExpr.

        expr = expr.replaceAll("\\*\\*", "^");

        return expr;
    }

    public List<String> readerToLines(Reader reader) {
        BufferedReader bufferedReader = new BufferedReader(reader);

        String lineRead;
        ArrayList<String> lines = new ArrayList<>();
        try {
            while ((lineRead = bufferedReader.readLine()) != null) {
                lines.add((StringUtils.chomp(lineRead.trim())));
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.err.println("Could not read lines from stream");
            System.exit(1);
        }

        return lines;
    }

    public CompiledExpression digFileToInvariantsConjunction(Reader digFile) {
        List<String> lines = readerToLines(digFile);
        boolean invstart = false;
        ArrayList<String> invariants = new ArrayList<>();

        for (String line : lines) {
            if (invstart) {
                // Strip out the starting "1.", "2.", etc. from the line.
                String strippedLine = line.replaceFirst("^\\d+\\.\\s*", "");

                if (strippedLine.isEmpty()) {
                    throw new IllegalArgumentException(
                        "Invariant starts with 1., 2., etc., but no valid content after stripping."
                    );
                }
                invariants.add(preProcessExpr(strippedLine));
            }

            if (line.contains("vtrace")) invstart = true;
        }

        return generateSMTFragmentsFor(invariants);
    }

    public CompiledExpression daikonFileToInvariantsConjunction(
        Reader daikonFile
    ) {
        List<String> lines = readerToLines(daikonFile);
        ArrayList<String> invariants = new ArrayList<>();
        boolean invstart = false;

        for (String line : lines) {
            if (line.contains("Exiting")) break;
            if (invstart) {
                if (!line.isEmpty() && !line.contains("one of")) {
                    invariants.add(preProcessExpr(line));
                }
            }
            if (line.contains("Faker")) invstart = true;
        }

        return generateSMTFragmentsFor(invariants);
    }

    /**
     * Generates SMT-LIB (S-expression) fragments for a list of invariant expressions.
     *
     * <p>This method processes a list of string representations of invariants, converts them into
     * Java expressions, captures variables used within those expressions, and transforms them
     * into corresponding SMT-LIB S-expressions. It then combines these S-expressions into a single
     * logical expression wrapped in an "and" clause. If no invariants are provided, the method defaults
     * to returning a "true" expression.</p>
     *
     * @param invariants An {@code ArrayList<String>} containing string representations of invariant expressions.
     * @return A {@code CompiledExpression} object that contains:
     *         <ul>
     *         <li>A set of captured variables used in the expressions.</li>
     *         <li>A combined SMT-LIB S-expression representing all the invariants.</li>
     *         </ul>
     */
    private CompiledExpression generateSMTFragmentsFor(
        List<String> invariants
    ) {
        HashSet<String> capturedVariables = new HashSet<>();
        ArrayList<String> sExpressions = new ArrayList<>();
        for (String invariant : invariants) {
            JavaExpr2SExpr expr2SExpr = new JavaExpr2SExpr();
            GetAllSimpleNames variableCapturer = new GetAllSimpleNames();

            String processedExpr = preProcessExpr(invariant);
            Expression javaExpr = generateJavaExpressionFromString(
                processedExpr
            );

            javaExpr.accept(expr2SExpr, null);
            javaExpr.accept(variableCapturer, null);

            String sExpression = expr2SExpr.getExpr();
            HashSet<String> variables = variableCapturer.getAllVars();

            sExpressions.add(sExpression);
            capturedVariables.addAll(variables);
        }

        CompiledExpression compiledExpression = new CompiledExpression();
        compiledExpression.variables = capturedVariables;

        StringBuilder combinedExpr = new StringBuilder();
        if (sExpressions.size() == 0) {
            combinedExpr.append("true");
        } else {
            combinedExpr.append("(and ");
            for (String sExpr : sExpressions) {
                combinedExpr.append(sExpr);
                combinedExpr.append(" ");
            }
            combinedExpr.append(")");
        }

        compiledExpression.sExpr = combinedExpr.toString();
        return compiledExpression;
    }

    /**
     * Parses a string representation of a Java expression and returns the corresponding {@code Expression} object.
     *
     * <p>This method first preprocesses the input string using {@code InvCompiler.preProcessExpr(String)} to ensure the
     * expression is properly formatted. Then, it attempts to parse the string into a Java expression using the
     * {@code JavaParser} library. If the parsing is successful, it returns the parsed {@code Expression}. If parsing fails
     * or the result is null, it throws an {@code IllegalArgumentException}.</p>
     *
     * @param expr The string representation of the Java expression to parse.
     * @return The parsed {@code Expression} object.
     * @throws IllegalArgumentException if the expression cannot be parsed or if parsing returns null.
     */
    public static Expression generateJavaExpressionFromString(String expr) {
        // Preprocess the expr. Very important
        expr = InvCompiler.preProcessExpr(expr);

        JavaParser parse = new JavaParser();
        ParseResult<Expression> result = parse.parseExpression(expr);
        if (result.isSuccessful()) {
            Expression rval = result.getResult().orElse(null);
            if (rval == null) {
                throw new IllegalArgumentException(
                    "Failed to parse the expression"
                );
            }

            return rval;
        } else {
            throw new IllegalArgumentException(
                "Failed to parse the expression because of " +
                result.getProblems() +
                "\n" +
                "The input string expression was '" +
                expr +
                "'\n"
            );
        }
    }
}
