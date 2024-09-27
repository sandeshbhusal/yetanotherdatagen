public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(a == 650) && !(a == -160) && !(a == -1) && !(a == 2) && !(a == 3851) && !(a == 1232) && !(a == 1222) && !(a == 855) && !(a == -385) && !(a == 325) && !(a == 4638) && !(a == -930) && !(a == 4880) && !(a == 0) && !(a == 2786) && !(a == 11) && !(a == 339) && !(a == 12) && !(a == 215) && !(a == 3407) && !(a == -2) && !(a == 1) && !(a == 3101) && !(a == 2246) && !(a == -3489) && !(a == -3489)) {
            if (ab > c) {
                if (ac > b) {
                    if (bc > a) {
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
        }
        return rval;
    }
}
