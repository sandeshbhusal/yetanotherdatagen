import edu.boisestate.datagen.reporting.*;

// Source: data/benchmarks/accelerating_invariant_generation/dagger/ex1.c
// #include <stdlib.h>
// #define assume(e) if(!(e)) exit(-1);
// extern int unknown_int(void);
// int nondet_int();
// int main () {
// int x;
// int y;
// int xa = 0;
// int ya = 0;
// while (unknown_int()) {
// x = xa + 2*ya;
// y = -2*xa + ya;
// x++;
// if (unknown_int()) y    = y+x;
// else y = y-x;
// xa = x - 2*y;
// ya = 2*x + y;
// }
// {;
// //@ assert(xa + 2*ya >= 0);
// }
// return 0;
// }
public class DaggerEX1 {

    public static void test(int a, int b) {
        int x;
        int y;
        int xa = 0;
        int ya = 0;
        Report.datagen_guard_instrument(10458, "funcguard", "a", a, "b", b);
        while (a > 0) {
            x = xa + 2 * ya;
            y = -2 * xa + ya;
            x++;
            if (b > 0)
                y = y + x;
            else
                y = y - x;
            xa = x - 2 * y;
            ya = 2 * x + y;
            a--;
        }
        Report.datagen_instrument(10458, "endfunc", "xa", xa, "ya", ya);
    }
}
