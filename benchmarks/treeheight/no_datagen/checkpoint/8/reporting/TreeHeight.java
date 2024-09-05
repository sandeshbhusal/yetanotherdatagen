import edu.boisestate.datagen.reporting.*;

public class TreeHeight {

    public int height(int[] tree) {
        if (tree == null || tree.length == 0) {
            return 0;
        }
        if (tree.length == 1) {
            return 1;
        }
        int length = tree.length;
        int leftheight;
        int rightheight;
        int height = 0;
        Report.datagen_guard_instrument("treeguard", "length", length);
        // Get left and right halves of the tree.
        int[] left = new int[length / 2];
        int[] right = new int[length / 2];
        for (int i = 0; i < length / 2; i++) {
            left[i] = tree[i];
            right[i] = tree[i + length / 2];
        }
        leftheight = height(left);
        rightheight = height(right);
        height = Math.max(leftheight, rightheight);
        Report.datagen_instrument("treeheight", "leftheight", leftheight, "rightheight", rightheight);
        return 1 + height;
    }
}
