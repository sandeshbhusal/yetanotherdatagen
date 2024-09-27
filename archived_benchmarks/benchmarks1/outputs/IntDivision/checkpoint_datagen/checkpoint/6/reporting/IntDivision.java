import edu.boisestate.datagen.reporting.*;

public class IntDivision {

    public void dividie(int a, int b) {
        Report.datagen_guard_instrument(12883, "outerguard", "a", a, "b", b);
        if (a >= b) {
            int q = 0;
            int r = a;
            Report.datagen_instrument(12883, "entermethod", "a", a, "b", b);
            while (r >= b) {
                Report.datagen_instrument(12883, "loopcondition", "a", a, "b", b, "q", q, "r", r);
                r -= b;
                q += 1;
            }
            Report.datagen_instrument(12883, "div_end", "a", a, "b", b, "q", q, "r", r);
        }
    }
}
