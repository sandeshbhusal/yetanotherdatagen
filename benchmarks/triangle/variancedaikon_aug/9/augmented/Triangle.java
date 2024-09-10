import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(a == 1411) && !(a == 3720) && !(a == -2452) && !(a == 5012) && !(a == 3865) && !(a == 128) && !(a == 280) && !(a == -1034) && !(a == 2) && !(a == 0) && !(a == 652) && !(a == -2064) && !(a == -658) && !(a == -24) && !(a == 2076) && !(a == -1) && !(a == 19) && !(a == 8) && !(a == -1031) && !(a == 1) && !(a == 4741) && !(a == 1419) && !(a == 2438) && !(a == 281) && !(a == 281)) {
            if (ab > c) {
                if (bc > a) {
                    if (ac > b) {
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
    }
}
