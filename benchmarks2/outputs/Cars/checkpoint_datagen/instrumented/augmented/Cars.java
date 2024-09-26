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
        if (true && !(v3 == 591) && !(v3 == 4931) && !(v3 == -800) && !(v3 == 3) && !(v3 == 2639) && !(v3 == 1088) && !(v3 == -5) && !(v3 == -533) && !(v3 == 1825) && !(v3 == -4675) && !(v3 == 778) && !(v3 == 3354) && !(v3 == -1307) && !(v3 == 1542) && !(v3 == 1304) && !(v3 == -50) && !(v3 == 1036) && !(v3 == 1354) && !(v3 == 1284) && !(v3 == 2346) && !(v3 == -558) && !(v3 == -2855) && !(v3 == 2063) && !(v3 == 4) && !(v3 == -1059) && !(v3 == 0) && !(v3 == -5169) && !(v3 == -591) && !(v3 == -1038) && !(v3 == -815) && !(v3 == 772) && !(v3 == 2594) && !(v3 == 1) && !(v3 == 296) && !(v3 == -6930) && !(v3 == 2330) && !(v3 == -4415) && !(v3 == 2074) && !(v3 == -513) && !(v3 == 4627) && !(v3 == 2564) && !(v3 == -1061) && !(v3 == 67) && !(v3 == 3348) && !(v3 == -1836) && !(v3 == -6213) && !(v3 == 2) && !(v3 == -2840) && !(v3 == 3589) && !(v3 == -1035) && !(v3 == 2609) && !(v3 == 2308) && !(v3 == 1838) && !(v3 == -1) && !(v3 == 529) && !(v3 == 285) && !(v3 == -1346) && !(v3 == -261) && !(v3 == 2846) && !(v3 == 40) && !(v3 == -1025) && !(v3 == 1837) && !(v3 == 838) && !(v3 == 2307) && !(v3 == -554) && !(v3 == 1552) && !(v3 == -829) && !(v3 == -1830) && !(v3 == -2326) && !(v3 == 1823) && !(v3 == 3633) && !(v3 == 75) && !(v3 == 5) && !(v3 == 1332) && !(v3 == -6456) && !(v3 == 6) && !(v3 == 2561) && !(v3 == -2357) && !(v3 == -772) && !(v3 == 1031) && !(v3 == -3371) && !(v3 == 256) && !(v3 == 256)) {
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
