public class Cars {

    public static void cars(int unknown_int, boolean innerif, int v1, int v2, int v3) {
        int x1 = 100;
        int x2 = 75;
        int x3 = -50;
        int t = 0;
        boolean cond1 = (v3 >= 0);
        boolean cond2 = (v1 <= 5);
        boolean cond3 = (v1 - v3 >= 0);
        boolean cond4 = (2 * v2 - v1 - v3 == 0);
        boolean cond5 = (v2 + 5 >= 0);
        boolean cond6 = (v2 <= 5);
        // Beginning assertions.
        // if these are false, we don't even enter the loop.
        // Run instrumentation at the end, and in the loop for v2.
        // Original Assertions
        // assert v1 <= 5 : "Assertion failed: v1 <= 5";
        // assert 2 * v2 + 2 * t >= v1 + v3 : "Assertion failed: 2*v2 + 2*t >= v1 + v3";
        // assert 5 * t + 75 >= x2 : "Assertion failed: 5*t + 75 >= x2";
        // assert v2 <= 6 : "Assertion failed: v2 <= 6";
        // assert v3 >= 0 : "Assertion failed: v3 >= 0";
        // assert v2 + 6 >= 0 : "Assertion failed: v2 + 6 >= 0";
        // assert x2 + 5 * t >= 75 : "Assertion failed: x2 + 5*t >= 75";
        // assert v1 - 2 * v2 + v3 + 2 * t >= 0 : "Assertion failed: v1 - 2*v2 + v3 + 2*t >= 0";
        // assert v1 - v3 >= 0 : "Assertion failed: v1 - v3 >= 0";
        if (true && !(unknown_int == 2564) && !(unknown_int == 529) && !(unknown_int == -573) && !(unknown_int == -6930) && !(unknown_int == -1061) && !(unknown_int == -807) && !(unknown_int == 3589) && !(unknown_int == 0) && !(unknown_int == -289) && !(unknown_int == -64) && !(unknown_int == -4132) && !(unknown_int == -3631) && !(unknown_int == 1) && !(unknown_int == -1) && !(unknown_int == 2308) && !(unknown_int == 2838) && !(unknown_int == -50) && !(unknown_int == 2316) && !(unknown_int == -3849) && !(unknown_int == -1119) && !(unknown_int == -1890) && !(unknown_int == 2) && !(unknown_int == -558) && !(unknown_int == -850) && !(unknown_int == 278) && !(unknown_int == -5169) && !(unknown_int == 3158) && !(unknown_int == 1115) && !(unknown_int == 3) && !(unknown_int == 2330) && !(unknown_int == 2594) && !(unknown_int == -2651) && !(unknown_int == 1887) && !(unknown_int == -1617) && !(unknown_int == 1348) && !(unknown_int == 4) && !(unknown_int == -2855) && !(unknown_int == 100) && !(unknown_int == 5) && !(unknown_int == 1304) && !(unknown_int == -1830) && !(unknown_int == 1312) && !(unknown_int == -1105) && !(unknown_int == -3928) && !(unknown_int == -5) && !(unknown_int == -533) && !(unknown_int == 1825) && !(unknown_int == -2326) && !(unknown_int == 2639) && !(unknown_int == 2846) && !(unknown_int == 1088) && !(unknown_int == 611) && !(unknown_int == -2357) && !(unknown_int == 256) && !(unknown_int == -1035) && !(unknown_int == 80) && !(unknown_int == 526) && !(unknown_int == 591) && !(unknown_int == 6) && !(unknown_int == 1552) && !(unknown_int == -1545) && !(unknown_int == -1121) && !(unknown_int == -1121)) {
            if (cond1 && cond2 && cond3 && cond4 && cond5 && cond6) {
                while (unknown_int > 0) {
                    boolean c1 = v2 + 5 >= 0;
                    boolean c2 = v2 <= 5;
                    if (!(c1 && c2))
                        break;
                    // assume(v2 + 5 >= 0);
                    // assume(v2 <= 5);
                    if (innerif) {
                        // assume(2 * x2 - x1 - x3 >= 0);
                        x1 = x1 + v1;
                        x3 = x3 + v3;
                        x2 = x2 + v2;
                        v2 = v2 - 1;
                        t = t + 1;
                    } else {
                        // assume(2 * x2 - x1 - x3 <= 0);
                        x1 = x1 + v1;
                        x3 = x3 + v3;
                        x2 = x2 + v2;
                        v2 = v2 + 1;
                        t = t + 1;
                    }
                    unknown_int -= 1;
                }
            }
            // datagen_guard_end
            ;
            // datagen_instrument exitloop v1 v2 v3 t
            ;
        }
    }
}
