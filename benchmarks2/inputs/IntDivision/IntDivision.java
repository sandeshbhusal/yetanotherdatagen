public class IntDivision {
    public void dividie(int a, int b) {

        // datagen_guard_start outerguard a b
        ;
        if (a >= b) {
            int q = 0;
            int r = a;

            // datagen_instrument entermethod a b
            ;

            while (r >= b) {
                // datagen_instrument loopcondition a b q r
                ;

                r -= b;
                q += 1;
            }

            // datagen_instrument div_end a b q r
            ;


        }
        // datagen_guard_end outerguard
	;
    } 
}
