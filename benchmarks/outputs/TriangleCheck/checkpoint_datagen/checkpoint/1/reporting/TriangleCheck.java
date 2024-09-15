import edu.boisestate.datagen.reporting.*;

public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        Report.datagen_guard_instrument(15759, "check_triangle", "a", a, "b", b, "c", c);
        if (ab > c) {
            if (ac > b) {
                if (bc > a) {
                    Report.datagen_instrument(15759, "triangle_ok", "a", a, "b", b, "c", c, "ab", ab, "ac", ac, "bc", bc);
                    rval = true;
                } else {
                    Report.datagen_instrument(15759, "triangle_not_ok_ab_ac_ok", "a", a, "b", b, "c", c, "ab", ab, "ac", ac, "bc", bc);
                    rval = false;
                }
            } else {
                Report.datagen_instrument(15759, "triangle_not_ok_ab_ok", "a", a, "b", b, "c", c, "ab", ab, "ac", ac, "bc", bc);
                rval = false;
            }
        } else {
            Report.datagen_instrument(15759, "triangle_not_ok", "a", a, "b", b, "c", c, "ab", ab, "ac", ac, "bc", bc);
            rval = false;
        }
        return rval;
    }
}
