import edu.boisestate.datagen.reporting.*;

public class Ex1 {

    public static void ex1(int outerloop, int condition, int xa, int ya) {
        int x = 0;
        int y = 0;
        // Original Assertion
        // assert xa + 2 * ya >= 0 : "Assertion failed: xa + 2*ya >= 0";
        Report.datagen_guard_instrument(15781, "entermethod", "outerloop", outerloop, "condition", condition, "x", x, "y", y);
        while (outerloop > 0) {
            x = xa + 2 * ya;
            y = -2 * xa + ya;
            x++;
            if (condition > 0) {
                y = y + x;
            } else {
                y = y - x;
            }
            xa = x - 2 * y;
            ya = 2 * x + y;
            outerloop -= 1;
        }
        Report.datagen_instrument(15781, "exitmethod", "xa", xa, "ya", ya);
    }
}
