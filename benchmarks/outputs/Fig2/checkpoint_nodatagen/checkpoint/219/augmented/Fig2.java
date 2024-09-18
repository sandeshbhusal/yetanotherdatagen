import java.util.Random;

public class Fig2 {

    public static void fig2(int outerloop, int firstif, int secondif) {
        int x = 0, y = 0, z = 0, w = 0;
        // Original Assertion
        // assert 3 * x >= y
        if (true) {
            while (outerloop > 0) {
                if (firstif > 0) {
                    x++;
                    y = y + 2;
                } else if (secondif > 0) {
                    if (x >= 4) {
                        x++;
                        y = y + 3;
                        z = z + 10;
                        w = w + 10;
                    }
                } else if (x >= z && w > y) {
                    x = -x;
                    y = -y;
                }
            }
        }
    }
}
