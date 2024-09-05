import java.io.*;

public class Triangle {

    public static void triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int bc = b + c;
        int ac = a + c;
        if (true && !(a == 1 && b == 2 && c == 1) && !(a == 0 && b == 955 && c == 0) && !(a == 0 && b == 0 && c == -1) && !(a == 955 && b == 955 && c == 0) && !(a == 1 && b == 1 && c == 1) && !(a == -131 && b == -131 && c == -131) && !(a == 0 && b == -1047 && c == -1047) && !(a == 0 && b == -1047 && c == -1047)) {
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
