import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(a == 0) && !(a == 2) && !(a == -464) && !(a == -517) && !(a == 646) && !(a == -1) && !(a == 328) && !(a == 1280) && !(a == -5395) && !(a == 3461) && !(a == 652) && !(a == 667) && !(a == 33) && !(a == 2511) && !(a == 963) && !(a == 1691) && !(a == 1) && !(a == 2714) && !(a == 1628) && !(a == 1413) && !(a == 578) && !(a == -1225) && !(a == -1225)) {
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
