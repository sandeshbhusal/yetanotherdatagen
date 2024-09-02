# no_datagen:

We don't really see many invariants here.

It seems like the equality operator binds very strongly with the genetic 
algorithm implementation of Evosuite.

// Loop invariants from DIG

vtrace1 (12 invs):
1. q - 1 == 0
2. a - b - r == 0
3. r**2 - 2340*r == 0
4. -a + b <= 0
5. -b + r <= -1
6. q - 1 - min(a, 0) == 0
7. min(b, 0) - q - 1 == 0
8. q - 1 - min(r, 0) == 0
9. min(a, b, 0) - q - 1 == 0
10. min(a, r, 0) - q - 1 == 0
11. min(b, r, 0) - q - 1 == 0
12. min(a, b, r, 0) - q - 1 == 0

DAIKON invariants:

Daikon version 5.8.18, released June 23, 2023; http://plse.cs.washington.edu/daikon.
Processing trace data; reading 1 dtrace file:                                  
[2024-09-02T01:06:28.306715]: Finished reading div.dtrace                      
===========================================================================    
Faker.fakemethod(int, int, int, int):::DATAGEN
q == 1
r one of { 0, 2340 }
a >= q
a >= b
a > r
q <= b
q != r
b > r
a - b - r == 0
Exiting Daikon.

# with datagen:

WOOHOO! We have results!
This is the 6th iteration, but we have resultsss!
This took a heckton of time to compute on my M3 though, which is funny.

4th iteration also has results. 33K points.

root@af897a80e947:/dig/src# ~/miniconda3/bin/python -O dig.py /sandesh/loopcondition.csv 
settings:INFO:2024-09-02 07:19:53.746655: dig.py /sandesh/loopcondition.csv
alg:INFO:analyzing '/sandesh/loopcondition.csv'
alg:INFO:got 57666 traces over 1 locs
alg:INFO:check 43 invs using 57666 traces (36.28s)
alg:INFO:simplify 43 invs (0.77s)
vtrace1 (6 invs):
1. a - b*q - r == 0
2. -q <= 0
3. b - r <= 0
4. -a + b <= 0
5. min(a, q) - r <= 0
6. q - 1 - max(a, r, 0) <= 0

There is something weird happening when negative numbers are in the play.
Normally, without datagen, we would not be able to get these results, but due
to negative numbers' division, we are seeing results (which are possible, but not normally)