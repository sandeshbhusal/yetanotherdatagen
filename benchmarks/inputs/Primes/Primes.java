// Source: data/benchmarks/sv-benchmarks/recursive/Primes.java
public class Primes {
    /* Function_mult */
    public static int mult(int n, int m) {
        if (m < 0) {
            return mult(n, -m);
        }
        if (m == 0) {
            return 0;
        }
        if (m == 1) {
            return n;
        }

        ; // datagen_instrument multiplication n m
        return n + mult(n, m - 1);
    }

    /* Function_multiple_of */
    public static int multipleOf(int n, int m) {
        if (m < 0) {
            return multipleOf(n, -m);
        }
        if (n < 0) {
            return multipleOf(-n, m);
        }
        if (m == 0) {
            return 0;
        }
        if (n == 0) {
            return 1;
        }
        return multipleOf(n - m, m);
    }

    public static int isPrime(int n) {
        int primecheck = 0;

        ; // datagen_guard_start global n

        primecheck = isPrime_(n, n - 1);

        if (primecheck == 1) {
            // assert that n > 1.
            ; // datagen_instrument prime_true n
        } else if (primecheck == 0) {
            // assert that n <= 1.
            ; // datagen_instrument prime_false n
        }

        ; // datagen_guard_end global

        return primecheck;
    }

    /* Function_is_prime_ */
    private static int isPrime_(int n, int m) {
        if (n <= 1) {
            return 0;
        }
        if (n == 2) {
            return 1;
        }
        if (n > 2) {
            if (m <= 1) {
                return 1;
            } else {
                if (multipleOf(n, m) == 0) {
                    return 0;
                }
                return isPrime_(n, m - 1);
            }
        }
        return 0;
    }
}

