package edu.boisestate.datagen;

import edu.boisestate.datagen.exprcompiler.*;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.LinkedList;
import org.tinylog.Logger;

public class Checkpoint {
    private static HashMap<String, LinkedList<Integer>> digIterations;
    private static HashMap<String, LinkedList<Integer>> daikonIterations;

    private static final int WINDOW_SIZE = 5;

    public Checkpoint(String className) {
        digIterations = new HashMap<>();
        daikonIterations = new HashMap<>();
    }

    public boolean checkChangeInWindow(String checkpointPath, String key, int currentIteration) {
        digIterations.putIfAbsent(key, new LinkedList<>());
        daikonIterations.putIfAbsent(key, new LinkedList<>());

        LinkedList<Integer> digList = digIterations.get(key);
        LinkedList<Integer> daikonList = daikonIterations.get(key);

        boolean digChanged = checkToolChange(checkpointPath, key, currentIteration, digList, "dig");
        boolean daikonChanged = checkToolChange(checkpointPath, key, currentIteration, daikonList, "daikon");

        if (digChanged || daikonChanged) {
            return true;
        }

        if (digList.size() >= WINDOW_SIZE && daikonList.size() >= WINDOW_SIZE) {
            Logger.debug("Invariants have stabilized for " + key + " at iteration " + currentIteration);
            return false;
        }

        return true;
    }

    private boolean checkToolChange(String checkpointPath, String key, int currentIteration,
                                    LinkedList<Integer> iterationList, String tool) {
        File currentFile = getToolFile(checkpointPath, currentIteration, key, tool);

        if (iterationList.isEmpty()) {
            iterationList.add(currentIteration);
            return true;
        }

        File previousFile = getToolFile(checkpointPath, iterationList.getLast(), key, tool);

        if (hasFileChanged(previousFile, currentFile)) {
            Logger.debug(tool.toUpperCase() + " has changed invariants between " +
                         iterationList.getLast() + " and " + currentIteration +
                         " for " + key + " reset to current iteration: " + currentIteration);
            iterationList.clear();
            iterationList.add(currentIteration);
            return true;
        } else {
            iterationList.add(currentIteration);
            if (iterationList.size() > WINDOW_SIZE) {
                iterationList.removeFirst();
            }
            return false;
        }
    }

    private File getToolFile(String checkpointPath, int iteration, String key, String tool) {
        File iterationDir = new File(String.format("%s/%d", checkpointPath, iteration));
        File codePath = new File(iterationDir, "code");
        return new File(codePath, key + "." + tool + "output");
    }

    public static boolean hasFileChanged(File file1, File file2) {
        boolean isDigFile = file1.getName().endsWith(".digoutput");
        InvCompiler compiler = new InvCompiler();

        try {
            if (isDigFile) {
                CompiledExpression ce1 = compiler.digFileToInvariantsConjunction(new FileReader(file1));
                CompiledExpression ce2 = compiler.digFileToInvariantsConjunction(new FileReader(file2));
                return (!ce1.equals(ce2));
            } else {
                String file1contents = new String(Files.readAllBytes(file1.toPath()));
                String file2contents = new String(Files.readAllBytes(file2.toPath()));

                if (file1contents.contains("one of") || file2contents.contains("one of")) {
                    return true;
                }

                CompiledExpression ce1 = compiler.daikonFileToInvariantsConjunction(new FileReader(file1));
                CompiledExpression ce2 = compiler.daikonFileToInvariantsConjunction(new FileReader(file2));
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
