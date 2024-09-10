import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(c == 1) && !(c == 198) && !(c == 994) && !(c == 1314) && !(c == 0) && !(c == 1124) && !(c == 1125) && !(c == 1575) && !(c == 4741) && !(c == -1) && !(c == -1031) && !(c == -1032) && !(c == -1032)) {
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
