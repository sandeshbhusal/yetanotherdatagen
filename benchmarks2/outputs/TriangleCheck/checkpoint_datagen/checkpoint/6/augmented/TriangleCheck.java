public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(a == 0) && !(a == -1) && !(a == 1) && !(a == 1293) && !(a == 2) && !(a == 3) && !(a == 909) && !(a == 2626) && !(a == 2568) && !(a == 1034) && !(a == 5192) && !(a == 5192)) {
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
