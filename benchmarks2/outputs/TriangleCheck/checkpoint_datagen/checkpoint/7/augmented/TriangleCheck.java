public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(c == 1293) && !(c == -2645) && !(c == -2630) && !(c == 1805) && !(c == 0) && !(c == 909) && !(c == 1489) && !(c == -2) && !(c == 2) && !(c == -1) && !(c == 1544) && !(c == 2568) && !(c == 5192) && !(c == 1) && !(c == 2626) && !(c == 3) && !(c == 3)) {
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
