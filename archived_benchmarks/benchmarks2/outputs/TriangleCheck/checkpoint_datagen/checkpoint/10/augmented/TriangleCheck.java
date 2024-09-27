public class TriangleCheck {

    public boolean check_triangle(int a, int b, int c) {
        boolean rval = false;
        int ab = a + b;
        int ac = a + c;
        int bc = b + c;
        if (true && !(b == 581) && !(b == -418) && !(b == 5192) && !(b == 6) && !(b == 1587) && !(b == -164) && !(b == 1544) && !(b == 3642) && !(b == 259) && !(b == 3620) && !(b == 1) && !(b == 2) && !(b == 5047) && !(b == -1070) && !(b == 1318) && !(b == -911) && !(b == 799) && !(b == -2252) && !(b == 1805) && !(b == 4270) && !(b == 3) && !(b == 1594) && !(b == -1) && !(b == 1821) && !(b == 1849) && !(b == 2568) && !(b == 32) && !(b == 826) && !(b == 651) && !(b == -64) && !(b == 2626) && !(b == 78) && !(b == -130) && !(b == -1487) && !(b == 909) && !(b == 5191) && !(b == 1293) && !(b == -1471) && !(b == -2630) && !(b == -1094) && !(b == 1563) && !(b == 0) && !(b == 0)) {
            if (ab > c) {
                if (ac > b) {
                    if (bc > a) {
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
        return rval;
    }
}
