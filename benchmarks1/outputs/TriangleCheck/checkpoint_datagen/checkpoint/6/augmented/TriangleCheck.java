public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(c == -385) && !(c == 3407) && !(c == 215) && !(c == 11) && !(c == 0) && !(c == 325) && !(c == -2) && !(c == -1812) && !(c == -1) && !(c == -591) && !(c == 650) && !(c == 1) && !(c == 2440) && !(c == 2440)) {
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
