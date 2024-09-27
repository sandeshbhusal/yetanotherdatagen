// #define assume(e) if(!(e)) exit(-1);
// int main()
// {
// int p;
// int i;
// int leader_len;
// int bufsize;
// int bufsize_0;
// int ielen;
// if(leader_len >0); else goto END;
// if(bufsize >0); else goto END;
// if(ielen >0); else goto END;
// if (bufsize < leader_len)
// goto END;
// p = 0;
// bufsize_0 = bufsize;
// bufsize -= leader_len;
// p += leader_len;
// if (bufsize < 2*ielen)
// goto END;
// for (i = 0; i < ielen && bufsize > 2; i++) {
// {;
// //@ assert(0<=p);
// }
// {;
// //@ assert(p+1<bufsize_0);
// }
// p += 2;
// }
// END:;
// }
public class MADWiFi {

    public void test(int leader_len, int bufsize, int ielen) {
        if (leader_len < 0)
            return;
        if (bufsize < 0)
            return;
        if (ielen < 0)
            return;
        if (bufsize < leader_len)
            return;
        if (true && !(leader_len == 0) && !(leader_len == 34) && !(leader_len == 1) && !(leader_len == 1)) {
            int p;
            int bufsize_0;
            p = 0;
            bufsize_0 = bufsize;
            bufsize -= leader_len;
            p += leader_len;
            if (bufsize < 2 * ielen)
                return;
            for (int i = 0; i < ielen && bufsize > 2; i++) {
                p += 2;
            }
        }
    }
}
