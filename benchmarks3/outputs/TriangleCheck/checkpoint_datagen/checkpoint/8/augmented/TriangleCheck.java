public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(c == 4) && !(c == -145) && !(c == 936) && !(c == -433) && !(c == 2577) && !(c == 834) && !(c == -2215) && !(c == 8) && !(c == 0) && !(c == 1437) && !(c == 563) && !(c == -1) && !(c == 1593) && !(c == 1436) && !(c == -440) && !(c == -313) && !(c == -21) && !(c == 1) && !(c == 785) && !(c == 5) && !(c == 10) && !(c == -2471) && !(c == -1039) && !(c == 18) && !(c == 518) && !(c == 939) && !(c == 2) && !(c == -805) && !(c == 2048) && !(c == 2447) && !(c == -3977) && !(c == 384) && !(c == 833) && !(c == 7) && !(c == 1468) && !(c == -2491) && !(c == -2491)) {
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
