// Source: data/benchmarks/accelerating_invariant_generation/dagger/Fig2.java
public class Fig2 {
    public static void fig2(int loopvar, boolean firstcond, boolean secondcond) {
        int x, y, z, w;
        x = y = z = w = 0;

        ; // datagen_guard_start funcguard loopvar
        // Simulating the while loop with unknownInt() condition
        while (loopvar) {
            if (firstcond) {
                x++;
                y = y + 2;
            } else if (secondcond) {
                if (x >= 4) {
                    x++;
                    y = y + 3;
                    z = z + 10;
                    w = w + 10;
                }
            } else if (x >= z && w > y) {
                x = -x;
                y = -y;
            }
        }
        ; // datagen_guard_end funcguard

        // Post-loop invariant assertion
        // assert 3 * x >= y : "Invariant violated: 3*x must be >= y";

        ; // datagen_instrument x y
    }
}
