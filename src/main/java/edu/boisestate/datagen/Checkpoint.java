package edu.boisestate.datagen;

import edu.boisestate.datagen.exprcompiler.*;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.util.HashMap;
import org.tinylog.Logger;

/* Checkpoint.java
 *
 * This class is used to store the checkpoint information for each program
 * instrumentation point to check if it is stable or not.
 */

public class Checkpoint {

    private static Checkpoint cp;
    private static HashMap<String, Integer> firstIterationForDig;
    private static HashMap<String, Integer> firstIterationForDaikon;

    // The window size to consider while checking for invariants' stability.
    private static final int WINDOW_SIZE = 3;

    public static Checkpoint getInstance() {
        if (cp == null) {
            cp = new Checkpoint();
        }
        return cp;
    }

    private Checkpoint() {
        firstIterationForDig = new HashMap<String, Integer>();
        firstIterationForDaikon = new HashMap<String, Integer>();
    }

    public void setFirstIterationForDig(String key, int value) {
        firstIterationForDig.put(key, value);
    }

    public void setFirstIterationForDaikon(String key, int value) {
        firstIterationForDaikon.put(key, value);
    }

    public int getFirstIterationForDig(String key) {
        return firstIterationForDig.get(key);
    }

    public int getFirstIterationForDaikon(String key) {
        return firstIterationForDaikon.get(key);
    }

    public boolean checkChangeInWindow(
        String checkpointPath,
        String key,
        int currentIteration
    ) {
        if (
            firstIterationForDig.containsKey(key) &&
            firstIterationForDaikon.containsKey(key)
        ) {
            int firstIterationDig = firstIterationForDig.get(key);
            int firstIterationDaikon = firstIterationForDaikon.get(key);

            boolean changedDig = false;
            boolean changedDaikon = false;

            // Need to do SMT checks.
            // We only need to check if the current iteration equals the firstIteration.
            // If it does, then the invariant is stable. Else, the firstIteration is reset
            // to the currentIteration.
            File firstCheckpointDirDaikon = new File(
                String.format("%s/%d", checkpointPath, firstIterationDig)
            );
            File firstCodePathDaikon = new File(
                firstCheckpointDirDaikon + "/code"
            );

            File iterationCheckpointDir = new File(
                String.format("%s/%d", checkpointPath, currentIteration)
            );
            File currentCodePath = new File(iterationCheckpointDir + "/code");

            File firstDaikonFile = new File(
                firstCodePathDaikon + "/" + key + ".daikonoutput"
            );
            File currentDaikonFile = new File(
                currentCodePath + "/" + key + ".daikonoutput"
            );

            if (hasFileChanged(firstDaikonFile, currentDaikonFile)) {
                changedDaikon = true;
                Logger.debug(
                    "Daikon has changed invariants between " +
                    firstIterationDaikon +
                    " and " +
                    currentIteration
                );
                firstIterationForDaikon.put(key, currentIteration);
            }

            // Do the same for DIG.
            File firstCheckpointDirDig = new File(
                String.format("%s/%d", checkpointPath, firstIterationDig)
            );

            File firstCodePathDig = new File(firstCheckpointDirDig + "/code");

            File firstDigFile = new File(
                firstCodePathDig + "/" + key + ".digoutput"
            );

            File currentDigFile = new File(
                currentCodePath + "/" + key + ".digoutput"
            );

            if (hasFileChanged(firstDigFile, currentDigFile)) {
                changedDig = true;
                Logger.debug(
                    "DIG has changed invariants between " +
                    firstIterationDig +
                    " and " +
                    currentIteration
                );
                firstIterationForDig.put(key, currentIteration);
            }

            boolean digStable = false;
            boolean daikonStable = false;

            if (!changedDig && currentIteration - firstIterationDig >= WINDOW_SIZE) {
                // Dig is stable now.
                Logger.debug("DIG is stable now for key " + key);
                digStable = true;
            }

            if (!changedDaikon && currentIteration - firstIterationDaikon >= WINDOW_SIZE) {
                // Daikon is stable now.
                Logger.debug("Daikon is stable now for key " + key);
                daikonStable = true;
            }

            return digStable && daikonStable;

        } else {
            // In the first iteration, there are no keys.
            firstIterationForDig.put(key, currentIteration);
            firstIterationForDaikon.put(key, currentIteration);

            // We always assume it has changed.
            return true;
        }
    }

    // private static boolean checkChangeInWindow(String key, int currentIteration) {}
    //

    // Semantic diff for invariants.
    public static boolean hasFileChanged(File file1, File file2) {
        boolean isDigFile = file1.getName().endsWith(".digoutput");
        InvCompiler compiler = new InvCompiler();

        try {
            if (isDigFile) {
                CompiledExpression ce1 =
                    compiler.digFileToInvariantsConjunction(
                        new FileReader(file1)
                    );

                CompiledExpression ce2 =
                    compiler.digFileToInvariantsConjunction(
                        new FileReader(file2)
                    );

                return (!ce1.equals(ce2));
            } else {
                // Daikon does not stabilize invariants very quickly. It
                // produces a bunch of "one of {x, y, z}" templates towards
                // the beginning, so if that is the case, we will skip comparing
                // invariants, as there are _no_ invariants generated at all.

                // Check if either file contains "one of".
                String file1contents = new String(
                    Files.readAllBytes(file1.toPath())
                );
                String file2contents = new String(
                    Files.readAllBytes(file2.toPath())
                );

                if (
                    file1contents.contains("one of") ||
                    file2contents.contains("one of")
                ) {
                    Logger.debug(
                        "Daikon invariants are too unstable to compare for " +
                        file1.getName()
                    );
                    // Invariants have not changed. Assume the file changed.
                    return true;
                }

                CompiledExpression ce1 =
                    compiler.daikonFileToInvariantsConjunction(
                        new FileReader(file1)
                    );
                CompiledExpression ce2 =
                    compiler.daikonFileToInvariantsConjunction(
                        new FileReader(file2)
                    );

                return (!ce1.equals(ce2));
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.out.println("Error reading invariant files for comparison.");
            System.exit(1);

            return false;
        }
    }
}
