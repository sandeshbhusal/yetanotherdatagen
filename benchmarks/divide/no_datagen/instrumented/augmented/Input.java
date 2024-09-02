public class Input {

    public void dividie(int a, int b) {
        // datagen_guard_end outerguard
        if (true) {
            if (a >= b) {
                int q = 0;
                int r = a;
                while (r >= b) {
                    r -= b;
                    q += 1;
                }
            }
        }
    }
}
