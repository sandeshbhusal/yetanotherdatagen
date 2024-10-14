public class TriangleCheck {
    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;

        ; // datagen_guard_start check_triangle a b c

        if (ab > c) {
            if (ac > b) {
                if (bc > a) {
                    ; // datagen_instrument triangle_ok a b c ab ac bc
                    rval = true;
                } else {
                    ; // datagen_instrument triangle_not_ok_ab_ac_ok a b c ab ac bc
                    rval = false;
                }
            } else {
                ; // datagen_instrument triangle_not_ok_ab_ok a b c ab ac bc
                rval = false;
            }
        } else {
            ; // datagen_instrument triangle_not_ok a b c ab ac bc
            rval = false;
        }

        ; // datagen_guard_end check_triangle
        return rval;
    }
}
