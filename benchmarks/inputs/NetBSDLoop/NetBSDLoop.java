public class NetBSDLoop {

    public static void NetBSDLoopTest(
        int MAXPATHLEN,
        int pathbufOff,
        int boundOff,
        int glob2PathbufOff,
        int glob2POff,
        int glob2PathlimOff
    ) {
        ; // datagen_guard_start funcguard MAXPATHLEN pathbufOff boundOff glob2POff
        if (MAXPATHLEN <= 0) {
            return;
        }

        pathbufOff = 0;
        boundOff = pathbufOff + (MAXPATHLEN + 1) - 1;

        glob2PathbufOff = pathbufOff;
        glob2PathlimOff = boundOff;

        for (glob2POff = glob2PathbufOff; glob2POff <= glob2PathlimOff; glob2POff++) {
            // Assert that invariants hold
            // assert 0 <= glob2POff : "Invariant violated: glob2POff must be >= 0";
            // assert glob2POff < MAXPATHLEN + 1 : "Invariant violated: glob2POff must be less than MAXPATHLEN + 1";

            ; // datagen_instrument glob glob2POff
            ; // datagen_instrument pathlen glob2POff MAXPATHLEN
        }

        ; // datagen_guard_end funcguard
    }
}
