public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(b == 813) && !(b == -2471) && !(b == 7) && !(b == 8) && !(b == 1771) && !(b == 2126) && !(b == 840) && !(b == 1) && !(b == 0) && !(b == 839) && !(b == 839)) {
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
