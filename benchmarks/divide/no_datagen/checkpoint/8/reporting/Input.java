import edu.boisestate.datagen.reporting.*;

public class Input {

    public void dividie(int a, int b) {
        // datagen_guard_end outerguard
        Report.datagen_guard_instrument("outerguard", "a", a, "b", b);
        if (a >= b) {
            int q = 0;
            int r = a;
            Report.datagen_instrument("entermethod", "a", a, "b", b);
            while (r >= b) {
                Report.datagen_instrument("loopcondition", "a", a, "b", b, "q", q, "r", r);
                r -= b;
                q += 1;
            }
            Report.datagen_instrument("div", "a", a, "b", b, "q", q, "r", r);
        }
    }
}
