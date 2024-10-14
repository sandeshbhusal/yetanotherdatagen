public class A_LT_B {
    public static boolean check_lt(int a, int b) {
        boolean rval = false;

        ; // datagen_guard_start entermethod a b

        if (a < b) {
            ; // datagen_instrument a_lt_b_truebranch a b

            rval = true;
        } else {
            ; // datagen_instrument a_lt_b_falsebranch a b

            rval = false;
        }

        ; // datagen_guard_end entermethod

        ; // datagen_instrument exitmethod_a_lt_b a b

        return rval;
    }
}
