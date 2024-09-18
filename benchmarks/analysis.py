# Analyze our benchmarks.

import os
import re
import glob
import sympy
from typing import List, Dict
from sympy import sympify, Eq, Le, Ge, Gt, Lt

def generate_sympy_scaffold(invariant: str):
    # Map string operators to SymPy operators
    operator_map = {
        "==": sympy.core.relational.Equality,
        "<=": sympy.core.relational.LessThan,
        ">=": sympy.core.relational.GreaterThan,
        "<": sympy.core.relational.StrictLessThan,
        ">": sympy.core.relational.StrictGreaterThan,
    }
    
    # Try matching the invariant with the correct operator
    for op_str, sympy_op in operator_map.items():
        if op_str in invariant:
            # Split the invariant using regular expression to handle spacing
            left, right = re.split(f"\\s*{re.escape(op_str)}\\s*", invariant)
            left = left.strip()  # Strip leading/trailing spaces from left-hand side
            right = right.strip()  # Strip leading/trailing spaces from right-hand side
            
            # Return the sympy operator, left, and right
            return (sympy_op, left, right)

    return None

def get_data_from_csv_file(file: str) -> List[Dict[str, int]]:
    rval = []
    with open(file) as infile:
        count = 0
        vars = []
        for line in infile:
            if count == 0:
                header = line
                header = header.split(';') 
                header = header[1:] #exclude the 'vtrace1' column.
                for var in header:
                    var = var.strip()
                    vars.append(var.strip().split()[1].strip())
            else:
                data = line.split(';')
                data = data[1:]
                combined = (dict(zip(vars, [int(x) for x in data])))
                rval.append(combined)
            count += 1
    return rval
 
class Info:
    def __init__(self):
        self.datagen_timetaken = 0
        self.totaliterations = 0
        self.datagen_stableiterations = {}
        self.dig_invariants = {}
        self.daikon_invariants = {}
        self.data_files = {}
        
    def __str__(self):
        return f"Time taken: {self.datagen_timetaken}\nTotal iterations: {self.totaliterations}\nStable iterations: {self.datagen_stableiterations}\nDig invariants: {self.dig_invariants}\nDaikon invariants: {self.daikon_invariants}\nData files: {self.data_files}"

def processdir(dir):
    datagen_tracefile = os.path.join(dir, 'trace.log')
    datagen_iterationcount = 0
    datagen_timetaken = 0
    datagen_stableiterations = {}

    datagen_dig_generated = {}
    datagen_daikon_generated = {}
    data_files = {}
    
    with open(datagen_tracefile, 'r') as f:
        for line in f:
            if 'Key' in line:
                # match the key.
                key = line.split()[1].strip(',')
                datagen_stableiterations[key] = line.split()[-1].strip()
            if 'Iteration' in line and 'took' in line:
                datagen_iterationcount += 1
                datagen_timetaken += int(line.split()[-2].strip())

    # Print generated invariants.
    for key in datagen_stableiterations.keys():
        datagen_daikon_generated[key] = []
        datagen_dig_generated[key] = []
       
    print(datagen_stableiterations) 
    for key in datagen_stableiterations.keys():
        # find file.
        daikon_invariants_file = os.path.join(dir, 'checkpoint', (datagen_stableiterations[key]), 'code', f"{key}.daikonoutput")
        dig_invariants_file = os.path.join(dir, 'checkpoint', (datagen_stableiterations[key]), 'code', f"{key}.digoutput")
        
        key_data_file = os.path.join(dir, 'checkpoint', (datagen_stableiterations[key]), 'code', f"{key}.csv")
        data_files[key] = key_data_file

        with open(daikon_invariants_file, 'r') as f:
            for line in f:
                if ('=' in line or '!=' in line or '>' in line or '<' in line) and '===' not in line:
                    try:
                        datagen_daikon_generated[key].append(line.strip())
                    except KeyError:
                        datagen_daikon_generated[key] = [line.strip()]

        with open(dig_invariants_file, 'r') as f:
            for line in f:
                if ('=' in line or '!=' in line or '>' in line or '<' in line) and '===' not in line:
                    line = ' '.join(line.split()[1:]) # Dig generates invariants like 1. a + b > c, so need to remove the numbering
                    try:
                        datagen_dig_generated[key].append(line.strip())
                    except KeyError:
                        datagen_dig_generated[key] = [line.strip()]

    information = Info()
    information.datagen_timetaken = datagen_timetaken
    information.totaliterations = datagen_iterationcount
    information.datagen_stableiterations = datagen_stableiterations
    information.dig_invariants = datagen_dig_generated
    information.daikon_invariants = datagen_daikon_generated
    information.data_files = data_files
    return information

for dirs in glob.glob('outputs/*'):
    benchname = (dirs.split('/')[-1])

    print("=" * 80)
    print(benchname)
    print("=" * 80)

    datagendir = os.path.join(dirs, 'checkpoint_datagen')
    nodatagendir = os.path.join(dirs, 'checkpoint_nodatagen')

    info = processdir (datagendir)
    print(info)
    print("-" * 80)
    info = processdir (nodatagendir)
    print(info)
    
    # try to get vars from info, and print them for one check.
    for ppt in info.data_files.keys():
        data = get_data_from_csv_file(info.data_files[ppt])
        print(data)
    break
