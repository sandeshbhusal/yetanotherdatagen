// // Source: data/benchmarks/accelerating_invariant_generation/invgen/bind_expands_vars2.c
// #include <stdlib.h>
// #define assume(e) if(!(e)) exit(-1);

// int main() {

//   int cp1_off, n1, n2, mc_i;
//   int MAXDATA;
//   if (MAXDATA > 0 ); else goto END;

//   if ((n1 <= MAXDATA * 2)); else goto END;

//   if ((cp1_off <= n1)); else goto END;

//   if ((n2 <= MAXDATA*2 - n1)); else goto END;

//   for (mc_i = 0; mc_i < n2; mc_i++) {

//     {;
// //@ assert(cp1_off+mc_i < MAXDATA * 2);
// }

//   }

//  END:  return 0;
// }

public class BindExpandsVars2 {
    public static void test(int cp1_off, int n1, int n2, int MAXDATA) {
        if (MAXDATA < 0)
            return;
        if (n1 < 0)
            return;
        if (n2 < 0)
            return;
        if (cp1_off < 0)
            return;
        if (n1 > MAXDATA * 2)
            return;
        if (cp1_off > n1)
            return;
        if (n2 > MAXDATA * 2 - n1)
            return;
        
        // datagen_instrument startingconds cp1_off n1 n2 MAXDATA
        ;

        // datagen_guard_start funcguard cp1_off n1 n2 MAXDATA
        ;

        int mc_i;
        for (mc_i = 0; mc_i < n2; mc_i++) {
            // datagen_instrument loopinvariant mc_i cp1_off MAXDATA
            ;
        }

        // datagen_guard_end funcguard
        ;
    }
}
