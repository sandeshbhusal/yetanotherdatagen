import java.io.*;
import edu.boisestate.datagen.reporting.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        Report.datagen_instrument("entermethod_triangle", "a", a, "b", b, "c", c);
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        Report.datagen_guard_instrument("majorguard", "a", a, "b", b, "c", c);
        if (ab > c) {
            Report.datagen_instrument("ab_gt_c", "a", a, "b", b, "c", c, "ab", ab);
            if (bc > a) {
                Report.datagen_instrument("bc_gt_a", "a", a, "b", b, "c", c, "ab", ab, "bc", bc);
                if (ac > b) {
                    Report.datagen_instrument("triangle_ok", "a", a, "b", b, "c", c, "ab", ab, "bc", bc, "ac", ac);
                    rval = true;
                } else {
                    rval = false;
                }
            } else {
                rval = false;
            }
        } else {
            rval = false;
        }
    }
}
