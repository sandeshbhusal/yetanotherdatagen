import java.io.*;

public class Input {
    public static void triangle(int a, int b, int c) {

        //datagen_instrument entermethod_triangle a b c
        ;

        boolean rval = false;
        
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
    
        // datagen_guard_start majorguard a b c
        ;

        if ( ab > c ) {
            //datagen_instrument ab_gt_c a b c ab
            ;

            if (bc > a) {
                //datagen_instrument ab_gt_c_and_bc_gt_a a b c ab bc
                ;

                if (ac > b) {
                    //datagen_instrument ab_gt_c_and_bc_gt_a_and_ac_gt_b a b c ab bc ac
                    ;

                    rval = true;

                } else {
                    rval = false;
                }
            } else {
                rval = false;
            }
        } else {
            rval = false;
        }

        // datagen_guard_end majorguard
        ;
    }
}