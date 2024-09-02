# Observations for this case

109 tests generated at the end of 10 iterations
Each iteration took roughly between 60-75 seconds, with increments about 2-3 seconds per iteration.

Invariants stabilized at iteration 3

Slower than running stuff without augmentation, obviously.

No datagen trace takes 10 seconds per iteration.
Invariant for only false branch stabilized at 4 iterations, but true path took 7 iterations to stabilize.

## With datagen
./9/code/a_lt_b_false.dtrace ->       47
./9/code/a_lt_b_true.dtrace ->       47
./9/code/entermethod.dtrace ->       94
./7/code/a_lt_b_false.dtrace ->       35
./7/code/a_lt_b_true.dtrace ->       35
./7/code/entermethod.dtrace ->       70
./6/code/a_lt_b_false.dtrace ->       28
./6/code/a_lt_b_true.dtrace ->       28
./6/code/entermethod.dtrace ->       56
./1/code/a_lt_b_false.dtrace ->        2
./1/code/a_lt_b_true.dtrace ->        1
./1/code/entermethod.dtrace ->        3
./10/code/a_lt_b_false.dtrace ->       55
./10/code/a_lt_b_true.dtrace ->       54
./10/code/entermethod.dtrace ->      109
./8/code/a_lt_b_false.dtrace ->       40
./8/code/a_lt_b_true.dtrace ->       41
./8/code/entermethod.dtrace ->       81
./4/code/a_lt_b_false.dtrace ->       19
./4/code/a_lt_b_true.dtrace ->       16
./4/code/entermethod.dtrace ->       35
./3/code/a_lt_b_false.dtrace ->       13
./3/code/a_lt_b_true.dtrace ->       10
./3/code/entermethod.dtrace ->       23
./2/code/a_lt_b_false.dtrace ->        6
./2/code/a_lt_b_true.dtrace ->        5
./2/code/entermethod.dtrace ->       11
./5/code/a_lt_b_false.dtrace ->       23
./5/code/a_lt_b_true.dtrace ->       22
./5/code/entermethod.dtrace ->       45

---

## Without datagen
./checkpoint/9/code/a_lt_b_false.dtrace ->       12
./checkpoint/9/code/a_lt_b_true.dtrace ->        9
./checkpoint/9/code/entermethod.dtrace ->       21
./checkpoint/7/code/a_lt_b_false.dtrace ->       11
./checkpoint/7/code/a_lt_b_true.dtrace ->        7
./checkpoint/7/code/entermethod.dtrace ->       18
./checkpoint/6/code/a_lt_b_false.dtrace ->       10
./checkpoint/6/code/a_lt_b_true.dtrace ->        6
./checkpoint/6/code/entermethod.dtrace ->       16
./checkpoint/1/code/a_lt_b_false.dtrace ->        2
./checkpoint/1/code/a_lt_b_true.dtrace ->        1
./checkpoint/1/code/entermethod.dtrace ->        3
./checkpoint/10/code/a_lt_b_false.dtrace ->       14
./checkpoint/10/code/a_lt_b_true.dtrace ->       10
./checkpoint/10/code/entermethod.dtrace ->       24
./checkpoint/8/code/a_lt_b_false.dtrace ->       12
./checkpoint/8/code/a_lt_b_true.dtrace ->        8
./checkpoint/8/code/entermethod.dtrace ->       20
./checkpoint/4/code/a_lt_b_false.dtrace ->        7
./checkpoint/4/code/a_lt_b_true.dtrace ->        4
./checkpoint/4/code/entermethod.dtrace ->       11
./checkpoint/3/code/a_lt_b_false.dtrace ->        5
./checkpoint/3/code/a_lt_b_true.dtrace ->        3
./checkpoint/3/code/entermethod.dtrace ->        8
./checkpoint/2/code/a_lt_b_false.dtrace ->        4
./checkpoint/2/code/a_lt_b_true.dtrace ->        2
./checkpoint/2/code/entermethod.dtrace ->        6
./checkpoint/5/code/a_lt_b_false.dtrace ->        9
./checkpoint/5/code/a_lt_b_true.dtrace ->        5
./checkpoint/5/code/entermethod.dtrace ->       14