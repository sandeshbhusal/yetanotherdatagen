import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(c == 1606) && !(c == -1225) && !(c == 2) && !(c == 963) && !(c == 1413) && !(c == -2) && !(c == 578) && !(c == 643) && !(c == -517) && !(c == 5441) && !(c == 0) && !(c == 838) && !(c == -1030) && !(c == 1) && !(c == 646) && !(c == -3) && !(c == 1280) && !(c == -1) && !(c == -1)) {
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
