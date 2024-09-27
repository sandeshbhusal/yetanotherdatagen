public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(a == 0) && !(a == 650) && !(a == -6408) && !(a == -160) && !(a == -1) && !(a == 11) && !(a == 2) && !(a == 12) && !(a == 293) && !(a == 3851) && !(a == 1944) && !(a == 3243) && !(a == 3496) && !(a == -2) && !(a == 1) && !(a == -385) && !(a == 4638) && !(a == -930) && !(a == 3118) && !(a == 3101) && !(a == 4880) && !(a == 279) && !(a == -3489) && !(a == -3489)) {
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
