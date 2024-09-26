import java.util.Random;
import edu.boisestate.datagen.reporting.*;

public class Fig2 {

    public static void fig2(int outerloop, int firstif, int secondif) {
        int x = 0, y = 0, z = 0, w = 0;
        // Original Assertion
        // assert 3 * x >= y
        Report.datagen_guard_instrument(13653, "entermethod", "outerloop", outerloop, "firstif", firstif, "secondif", secondif);
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
        Report.datagen_instrument(13653, "exitloop", "x", x, "y", y);
    }
}
