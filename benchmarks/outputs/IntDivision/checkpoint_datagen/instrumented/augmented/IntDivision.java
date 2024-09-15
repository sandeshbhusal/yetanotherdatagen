public class IntDivision {

    public void divide(int dividend, int divisor) {
        if (true) {
            if (dividend > divisor) {
                int q = 0;
                int r = dividend;
                while (r >= divisor) {
                    r = r - divisor;
                    q = q + 1;
                }
            }
        }
    }
}
