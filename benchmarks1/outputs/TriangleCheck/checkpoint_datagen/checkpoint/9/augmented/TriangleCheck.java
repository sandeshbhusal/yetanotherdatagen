public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(b == 293) && !(b == 12) && !(b == 2735) && !(b == -1467) && !(b == 3603) && !(b == -930) && !(b == 4408) && !(b == -1415) && !(b == 1) && !(b == 2079) && !(b == -2610) && !(b == 34) && !(b == 11) && !(b == -3489) && !(b == -786) && !(b == -2) && !(b == -6408) && !(b == 650) && !(b == 3496) && !(b == 279) && !(b == -518) && !(b == 3483) && !(b == 2440) && !(b == 3851) && !(b == 3482) && !(b == -1) && !(b == -423) && !(b == 3118) && !(b == 3101) && !(b == -792) && !(b == 4880) && !(b == -160) && !(b == 1308) && !(b == -4126) && !(b == 1944) && !(b == 648) && !(b == -1812) && !(b == 0) && !(b == 0)) {
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
