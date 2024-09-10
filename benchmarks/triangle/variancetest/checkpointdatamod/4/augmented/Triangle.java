import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(c == -517) && !(c == 0) && !(c == 838) && !(c == 2) && !(c == 652) && !(c == 1) && !(c == 646) && !(c == 963) && !(c == -1) && !(c == -1)) {
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
