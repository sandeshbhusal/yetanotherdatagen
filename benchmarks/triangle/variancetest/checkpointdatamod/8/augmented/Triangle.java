import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(c == 2714) && !(c == 667) && !(c == -2344) && !(c == 2) && !(c == 1439) && !(c == 3249) && !(c == 2236) && !(c == -1055) && !(c == 314) && !(c == 1413) && !(c == 666) && !(c == 0) && !(c == -6) && !(c == 3086) && !(c == -1030) && !(c == 1) && !(c == 1343) && !(c == 1280) && !(c == -1) && !(c == -7) && !(c == -3978) && !(c == 652) && !(c == 5305) && !(c == -1457) && !(c == -184) && !(c == -2) && !(c == 643) && !(c == -517) && !(c == -1434) && !(c == -2226) && !(c == 549) && !(c == 646) && !(c == -3) && !(c == -1058) && !(c == -2363) && !(c == -2363)) {
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
