public class IntDivision {
    public void divide(int dividend, int divisor) {
        // datagen_guard_start divide_guard dividend divisor
        ;

        if (dividend > divisor) {
            int q = 0;
            int r = dividend;
            

            while (r >= divisor) {
                r = r - divisor;
                q = q + 1;

                // datagen_instrument loopinvariant dividend divisor q r
                ;
            }

            // datagen_instrument exitmethod dividend divisor q r
            ;
        }

        // datagen_guard_end divide_guard
        ;
    }    
}
