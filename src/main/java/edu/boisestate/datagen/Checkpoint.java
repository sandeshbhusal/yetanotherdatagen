package edu.boisestate.datagen;

import java.util.HashMap;

import org.tinylog.Logger;

import java.io.StringReader;

import edu.boisestate.datagen.exprcompiler.CompiledExpression;
import edu.boisestate.datagen.exprcompiler.InvCompiler;

public class Checkpoint {
    public static class CheckpointInformation {
        String content;
        int iteration;

        public CheckpointInformation(String content, int iteration) {
            this.content = content;
            this.iteration = iteration;
        }
    }

    private int windowSize;

    private HashMap<String, CheckpointInformation> compareForDig = new HashMap<>();
    private HashMap<String, CheckpointInformation> compareForDaikon = new HashMap<>();

    public Checkpoint(int windowSize) {
        this.windowSize = windowSize;
    }

    public int getConsideredIterationDaikon(String key) {
        CheckpointInformation cpi = this.compareForDaikon.get(key);
        if (cpi == null)
            return 0;
        return cpi.iteration;
    }

    // Returns if daikon content is different from the one we have stored.
    public boolean hasChangedDaikon(String key, int iteration, String content) {
        // If the content contains "one of", then the daikon invariant is not stable yet
        // so we do a early return.
        if (content.contains("one of")
                || (compareForDaikon.get(key) != null && compareForDaikon.get(key).content.contains("one of"))) {
            Logger.warn("Unstable key " + key + " for Daikon will be skipped.");
            CheckpointInformation resetInfo = new CheckpointInformation(content, iteration);
            this.compareForDaikon.put(key, resetInfo);
            return true;

        } else {
            CheckpointInformation storedInfo = compareForDaikon.get(key);
            // If we have nothing here, then return early.
            if (storedInfo == null) {
                CheckpointInformation resetInfo = new CheckpointInformation(content, iteration);
                this.compareForDaikon.put(key, resetInfo);
                return true;
            }
            String storedContents = compareForDaikon.get(key).content;

            // Check if the content is _exactly_ the same, i.e. text diff. If so,
            // these are the same (we do this to avoid doing expensive z3 analyses).
            if (content.equals(storedContents)) {
                // If content is the same, we leave the map as-is, since no change is
                // required, and return that the invariants have not changed at all.
                int windowSize = iteration - this.compareForDaikon.get(key).iteration;
                // If window is smaller, then the invariants have changed.
                return windowSize < this.windowSize;
            } else {
                // If the content is not exactly the same, we require a compiler
                InvCompiler compiler = new InvCompiler();

                CompiledExpression newExpr = compiler.daikonFileToInvariantsConjunction(new StringReader(content));
                CompiledExpression oldExpr = compiler
                        .daikonFileToInvariantsConjunction(new StringReader(storedContents));

                // If the expressions are different, that means our invariants have changed.
                // so we return early.
                if (!newExpr.equals(oldExpr)) {
                    // Store this as a new checkpoint, and return early.
                    CheckpointInformation resetInfo = new CheckpointInformation(content, iteration);
                    this.compareForDaikon.put(key, resetInfo);
                    return true;
                }
            }
        }

        // At this point, since we did not return early, the invariants generated
        // are exactly the same. So, we just need to check window size, i.e. if stored
        // iteration
        // exceeds the iteration # by window size.
        int windowSize = iteration - this.compareForDaikon.get(key).iteration;
        // if the window is smaller, then the invariants have changed.
        return windowSize < this.windowSize;
    }
}