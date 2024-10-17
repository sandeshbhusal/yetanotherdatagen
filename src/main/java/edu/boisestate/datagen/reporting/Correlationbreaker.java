package edu.boisestate.datagen.reporting;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.utils.Pair;

/* Correlationbreaker attempts to break the correlation between variables
 * It looks at the cache data for the given guard ID, and with a fixed
 * probability, generates NEQ expressions between variables if they are a
 * simple multiple of each other across all cases. It then returns this expression.
 * 
 * Correlationbreaker is implemented as a singleton that "listen"s to the cache change,
 * and updates the expression accordingly.
 * 
 * However, if the variables are truly correlated, this probability drops down. We start off
 * by assuming that the variables are all independent. As we find more dependence between
 * variables for the same slope, we decrease the probability and return a "true" as the only expression. 
 */

public class Correlationbreaker {
    private static HashMap<String, Float> probability = new HashMap<>();
    private static Correlationbreaker cb;

    private Correlationbreaker() {
    }

    public static Correlationbreaker getInstance() {
        if (cb == null) {
            cb = new Correlationbreaker();
        }
        return cb;
    }

    public Expression genExpression(String guardId, HashSet<HashMap<String, Object>> data) {
        // if no data is seen yet, nothing to break.
        if (data == null) {
            return new BooleanLiteralExpr(true);
        }

        // Convert this HashSet of HashMaps to a HashMap of HashSets (Integer values).
        HashMap<String, HashSet<Integer>> convertedData = new HashMap<>();

        for (HashMap<String, Object> item : data) {
            for (String key: item.keySet()){
                HashSet<Integer> innerData = convertedData.getOrDefault(key, new HashSet<>());
                // WARN: only works with ints.
                innerData.add((Integer) item.get(key));
                convertedData.put(key, innerData);
            } 
        }

        // Compute correlation between variables in the HashMap.
        HashMap<Integer, HashSet<Pair<String, String>>> correlationRanks = computeCorrelations(convertedData);

        // For the highest-correlated pair:
        if (!correlationRanks.isEmpty()) {
            int highestRank = correlationRanks.keySet().stream().max(Integer::compareTo).orElse(-1);
            HashSet<Pair<String, String>> highestCorrelatedPairs = correlationRanks.get(highestRank);

            if (!highestCorrelatedPairs.isEmpty()) {
                Pair<String, String> pair = highestCorrelatedPairs.iterator().next();
                String var1 = pair.a;
                String var2 = pair.b;
                String probabilityKey = guardId + "_" + var1 + "_" + var2;

                // Update probability
                float currentProb = probability.getOrDefault(probabilityKey, 1.0f);

                // If within 4 iterations we find 100% correlation, we will continue to treat these 
                // variables normally.

                float newProb = Math.max(0, currentProb - 0.25f);
                probability.put(probabilityKey, newProb);

                // Generate expression with a fixed threshold probability of 0.5f
                if (newProb >= 0.5f) {
                    int slope = computeSlope(convertedData.get(var1), convertedData.get(var2));
                    return new BinaryExpr(
                            new NameExpr(var1),
                            new BinaryExpr(
                                    new IntegerLiteralExpr(slope),
                                    new NameExpr(var2),
                                    BinaryExpr.Operator.MULTIPLY),
                            BinaryExpr.Operator.NOT_EQUALS);
                }
            }
        }

        // If no correlation found or probability is below threshold, return true
        return new BooleanLiteralExpr(true);
    }

    public static HashMap<Integer, HashSet<Pair<String, String>>> computeCorrelations(
            HashMap<String, HashSet<Integer>> data) {
        HashMap<Integer, HashSet<Pair<String, String>>> correlationRanks = new HashMap<>();

        // List of variables (column names)
        List<String> variables = new ArrayList<>(data.keySet());

        // Iterate over unique pairs of variables
        for (int i = 0; i < variables.size(); i++) {
            for (int j = i + 1; j < variables.size(); j++) {
                String var1 = variables.get(i);
                String var2 = variables.get(j);

                // Calculate slope using integers
                int slope = computeSlope(data.get(var1), data.get(var2));

                if (slope != Integer.MAX_VALUE && slope != 0) {
                    int rank = Math.abs(1 / slope); // Slope can't be zero or infinity here
                    correlationRanks
                            .computeIfAbsent(rank, k -> new HashSet<>())
                            .add(new Pair<>(var1, var2));
                }
            }
        }

        return correlationRanks;
    }

    // Computes the slope using integer arithmetic
    private static int computeSlope(HashSet<Integer> set1, HashSet<Integer> set2) {
        if (set1.size() != set2.size() || set1.size() < 2) {
            return Integer.MAX_VALUE; // Not enough data to calculate slope
        }

        // Convert HashSets to Lists for easier index-based access
        List<Integer> xValues = new ArrayList<>(set1);
        List<Integer> yValues = new ArrayList<>(set2);

        int n = xValues.size();
        int sumX = 0, sumY = 0, sumXY = 0, sumXX = 0;

        // Calculate sums for the least squares formula using integers
        for (int i = 0; i < n; i++) {
            int x = xValues.get(i);
            int y = yValues.get(i);
            sumX += x;
            sumY += y;
            sumXY += x * y;
            sumXX += x * x;
        }

        // Slope formula: (n * Σ(x*y) - Σx * Σy) / (n * Σ(x^2) - (Σx)^2)
        int numerator = n * sumXY - sumX * sumY;
        int denominator = n * sumXX - sumX * sumX;

        if (denominator == 0) {
            return Integer.MAX_VALUE; // Vertical line or no variation in x-values
        }

        return numerator / denominator;
    }
}
