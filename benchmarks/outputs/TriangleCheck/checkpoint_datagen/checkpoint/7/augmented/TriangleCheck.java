public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(b == 3) && !(b == 10) && !(b == 8) && !(b == -3539) && !(b == 5) && !(b == -1) && !(b == 2577) && !(b == 1) && !(b == 2447) && !(b == 839) && !(b == 785) && !(b == 837) && !(b == 969) && !(b == 18) && !(b == 7) && !(b == -3977) && !(b == 2126) && !(b == 834) && !(b == 840) && !(b == 0) && !(b == 838) && !(b == 838)) {
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
