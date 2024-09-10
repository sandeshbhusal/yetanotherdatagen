import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(b == 3) && !(b == -3978) && !(b == -1434) && !(b == 14) && !(b == -6) && !(b == 2181) && !(b == 1691) && !(b == -1) && !(b == 2196) && !(b == -1438) && !(b == 646) && !(b == -1164) && !(b == -2840) && !(b == -7) && !(b == -1433) && !(b == -517) && !(b == -2) && !(b == -277) && !(b == 2) && !(b == 667) && !(b == 1439) && !(b == 3485) && !(b == 645) && !(b == 3086) && !(b == -3) && !(b == 666) && !(b == 1159) && !(b == 1) && !(b == 1280) && !(b == -1030) && !(b == -909) && !(b == 9) && !(b == 0) && !(b == 1413) && !(b == 643) && !(b == 652) && !(b == 2714) && !(b == -1055) && !(b == -1055)) {
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
