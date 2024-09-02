import java.io.*;
import edu.boisestate.datagen.reporting.*;

public class Input {

    public static void intdiv(int a, int b) {
        Report.datagen_instrument("entermethod", "a", a, "b", b);
        Report.datagen_guard_instrument("outerguard", "a", a, "b", b);
        if (a < b) {
            Report.datagen_instrument("a_lt_b_true", "a", a, "b", b);
            boolean rval = true;
        } else {
            Report.datagen_instrument("a_lt_b_false", "a", a, "b", b);
            boolean rval = false;
        }
    }
}
