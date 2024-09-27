import edu.boisestate.datagen.reporting.*;

public class A_LT_B {

    public static boolean check_lt(int a, int b) {
        boolean rval = false;
        Report.datagen_guard_instrument(14199, "entermethod", "a", a, "b", b);
        if (a < b) {
            Report.datagen_instrument(14199, "a_lt_b_truebranch", "a", a, "b", b);
            rval = true;
        } else {
            Report.datagen_instrument(14199, "a_lt_b_falsebranch", "a", a, "b", b);
            rval = false;
        }
        Report.datagen_instrument(14199, "exitmethod_a_lt_b", "a", a, "b", b);
        return rval;
    }
}
