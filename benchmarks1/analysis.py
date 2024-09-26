# Analyze our benchmarks.

import os
import glob
from sympy import sympify, Eq, Le, Ge, Gt, Lt

class Info:
    def __init__(self):
        self.datagen_timetaken = 0
        self.totaliterations = 0
        self.datagen_stableiterations = {}
        self.invariants = {}

def processdir(dir):
    print("####################################### Processing %s" % dir)
    datagen_tracefile = os.path.join(dir, 'trace.log')
    datagen_iterationcount = 0
    datagen_timetaken = 0
    datagen_stableiterations = {}

    datagen_dig_generated = set()
    datagen_daikon_generated = set()

    print("Trace points:")
    with open(datagen_tracefile, 'r') as f:
        for line in f:
            if 'Key' in line:
                # match the key.
                key = line.split()[1].strip(',')
                print(key)
                datagen_stableiterations[key] = datagen_iterationcount
            if 'Iteration' in line and 'took' in line:
                datagen_iterationcount += 1
                datagen_timetaken += int(line.split()[-2].strip())

    print("Total time taken for datagen: %d seconds" % datagen_timetaken)
    print("Iterations taken for datagen: %d" % datagen_iterationcount)
    for key in datagen_stableiterations:
        print("Iterations taken for %s: %d" % (key, datagen_stableiterations[key]))
    
    # Print generated invariants.
    for key in datagen_stableiterations.keys():
        print("For point %s:" % key)
        # find file.
        daikon_invariants_file = os.path.join(dir, 'checkpoint', str(datagen_stableiterations[key]), 'code', f"{key}.daikonoutput")
        dig_invariants_file = os.path.join(dir, 'checkpoint', str(datagen_stableiterations[key]), 'code', f"{key}.digoutput")

        print("Generated DAIKON invariants:")
        with open(daikon_invariants_file, 'r') as f:
            for line in f:
                if ('=' in line or '!=' in line or '>' in line or '<' in line) and '=====' not in line:
                    datagen_daikon_generated.add(line.strip())
        print(datagen_daikon_generated)

        print("Generated DIG invariants:")
        with open(dig_invariants_file, 'r') as f:
            for line in f:
                if ('=' in line or '!=' in line or '>' in line or '<' in line) and '=====' not in line:
                    line = ' '.join(line.split()[1:]) # Dig generates invariants like 1. a + b > c, so need to remove the numbering
                    datagen_dig_generated.add(line.strip())
        print(datagen_dig_generated)

    datagen_valid_dig_invariants = set()
    datagen_valid_daikon_invariants = set()

    def generate_sympy_scaffold(invariant: str):
        left = right = op = None
        if "==" in invariant:
            op = Eq
            left, right = invariant.split("==")
        elif "<=" in invariant:
            op = Le
            left, right = invariant.split("<=")
        elif ">=" in invariant:
            op = Ge
            left, right = invariant.split(">=")
        elif "<" in invariant:
            op = Lt
            left, right = invariant.split("<")
        elif ">" in invariant:
            op = Gt
            left, right = invariant.split(">")
        return (op, left.strip(), right.strip())    


    for invariant in datagen_daikon_generated:
        datagen_valid_daikon_invariants.add(generate_sympy_scaffold(invariant))

    for invariant in datagen_dig_generated:
        datagen_valid_dig_invariants.add(generate_sympy_scaffold(invariant))
    
    # TODO: This is producing weird keys ??
    print(datagen_valid_dig_invariants)

    #---------------------- Repeat the same process for nodatagen -----------------------




            



for dirs in glob.glob('outputs/*'):
    benchname = (dirs.split('/')[-1])

    print("=" * 80)
    print(benchname)
    print("=" * 80)

    datagendir = os.path.join(dirs, 'checkpoint_datagen')
    nodatagendir = os.path.join(dirs, 'checkpoint_nodatagen')

    processdir (datagendir)
    break
