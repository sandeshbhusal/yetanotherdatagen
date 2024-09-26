public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(b == 518) && !(b == 806) && !(b == 5) && !(b == -1039) && !(b == 1) && !(b == 2447) && !(b == 785) && !(b == 2) && !(b == -4261) && !(b == -21) && !(b == 7) && !(b == -3977) && !(b == -145) && !(b == 2582) && !(b == 1437) && !(b == 2048) && !(b == 20) && !(b == -805) && !(b == -433) && !(b == 384) && !(b == 3) && !(b == 10) && !(b == -149) && !(b == 8) && !(b == 1551) && !(b == 1436) && !(b == 936) && !(b == -1) && !(b == 2577) && !(b == -4383) && !(b == 939) && !(b == 813) && !(b == 563) && !(b == 18) && !(b == -2471) && !(b == -2215) && !(b == 0) && !(b == 3978) && !(b == 3978)) {
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
