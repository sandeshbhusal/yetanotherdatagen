import edu.boisestate.datagen.reporting.*;

public class IntDivision {

    public void divide(int dividend, int divisor) {
        Report.datagen_guard_instrument(19037, "divide_guard", "dividend", dividend, "divisor", divisor);
        if (dividend > divisor) {
            int q = 0;
            int r = dividend;
            while (r >= divisor) {
                r = r - divisor;
                q = q + 1;
                Report.datagen_instrument(19037, "loopinvariant", "dividend", dividend, "divisor", divisor, "q", q, "r", r);
            }
            Report.datagen_instrument(19037, "exitmethod", "dividend", dividend, "divisor", divisor, "q", q, "r", r);
        }
    }
}
