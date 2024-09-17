public class Ex1 {
    public static void ex1(int outerloop, int condition, int xa, int ya) {
        int x = 0;
        int y = 0;
        
        // datagen_guard_start entermethod outerloop condition x y
        ;

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

        // datagen_guard_end entermethod
        ;

        // datagen_instrument exitmethod xa ya
        ;

        // Original Assertion
        // assert xa + 2 * ya >= 0 : "Assertion failed: xa + 2*ya >= 0";
    }
}

