# Analyze our benchmarks.

import os
import re
import glob
import json
import pandas as pd
import sympy
from typing import List, Dict
from sympy import sympify, Eq, Le, Ge, Gt, Lt

class Info:
    def __init__(self):
        self.datagen_timetaken = 0
        self.totaliterations = 0
        self.datagen_stableiterations = {}
        self.dig_invariants_str = {}
        self.daikon_invariants_str = {}
        self.dig_sympy = {}
        self.daikon_sympy = {}
        self.data_files = {}
        self.data = {}
        
    def __str__(self):
        counts = {}
        for key in self.data.keys():
            counts[key] = len(self.data[key])
            
        return f"Time taken: {self.datagen_timetaken}\nTotal iterations: {self.totaliterations}\nStable iterations: {self.datagen_stableiterations}\nDig invariants: {self.dig_invariants}\nDaikon invariants: {self.daikon_invariants}\nData files: {self.data_files}\n Data points count: {counts}"


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
       
    # print(datagen_stableiterations) 
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

    data = {}
    for key in datagen_stableiterations.keys():
        data[key] = get_data_from_csv_file(data_files[key]) 
    
    daikon_sympy = {}        
    dig_sympy = {}
    for key in datagen_stableiterations.keys():
        daikon_sympy[key] = []
        dig_sympy[key] = []
        
        # generate eval expressions from invariants. 
        for invariant in datagen_daikon_generated[key]:
            # print(invariant)
            sympy_invariant = generate_sympy_scaffold(invariant)
            if sympy_invariant is not None:
                daikon_sympy[key].append(sympy_invariant) 

        for invariant in datagen_dig_generated[key]:
            # print(invariant)
            sympy_invariant = generate_sympy_scaffold(invariant)
            if sympy_invariant is not None:
                dig_sympy[key].append(sympy_invariant)
                                                            
    information = Info()
    information.datagen_timetaken = datagen_timetaken
    information.totaliterations = datagen_iterationcount
    information.datagen_stableiterations = datagen_stableiterations
    information.dig_invariants_str = datagen_dig_generated
    information.daikon_invariants_str = datagen_daikon_generated
    information.dig_sympy = dig_sympy
    information.daikon_sympy = daikon_sympy
    information.data_files = data_files
    information.data = data
    return information

def check_if_same_invs(inv1, inv2) -> bool:
    op1, lhs1, rhs1 = inv1
    op2, lhs2, rhs2 = inv2
    return op1 == op2 and lhs1 == lhs2 and rhs1 == rhs2

bigresults = {}
for dirs in glob.glob('outputs/*'):
    benchname = (dirs.split('/')[-1])
    # if not ( benchname.startswith('Tri') or benchname.startswith("Car")):
    #     continue

    print("=" * 80)
    print(benchname)
    print("=" * 80)
    print("Processing dir")

    datagendir = os.path.join(dirs, 'checkpoint_datagen')
    nodatagendir = os.path.join(dirs, 'checkpoint_nodatagen')

    datagen_info = processdir(datagendir)
    nodatagen_info = processdir(nodatagendir)
    
    keys = set(datagen_info.datagen_stableiterations.keys())
    
    # Run innvalidation on the produced invariants, and print the results.
    
    # --- invvalidation ----
    # 1. Get data points from nodatagen
    # 2. evaluate expressions in datage.dig_sympy, and datagen.daikon_sympy (cross validation)
    # 3. If any data point causes the expr to evaluate to false, print it.
    
    datagen_proper_dig = {}
    datagen_proper_daikon = {} 
    datagen_deleted_invs_dig = {}
    datagen_deleted_invs_daikon = {}
    
    nodata_proper_dig = {}
    nodata_proper_daikon = {}
    nodata_deleted_invs_dig = {}
    nodata_deleted_invs_daikon = {}

    print("Validating datagen invariants")
    for (key, inv_exprs) in datagen_info.dig_sympy.items():
        datagen_proper_dig[key] = []
        datagen_deleted_invs_dig[key] = []
        
        for inv_expr in inv_exprs:
            op, lhs, rhs = inv_expr
            flag = True
            for data in nodatagen_info.data[key]:
                if not op(sympify(lhs, data), sympify(rhs, data)):
                    print(f"Invalid invariant: {inv_expr} for data point: {data}")
                    datagen_deleted_invs_dig[key].append(inv_expr)
                    flag = False
                    break
            if flag:
                datagen_proper_dig[key].append(inv_expr)
                
    # print("##### Final list of invariants produced by dig:")
    # for key in datagen_proper_dig.keys():
    #     print(f"Key: {key}")
    #     for inv in datagen_proper_dig[key]:
    #         op, lhs, rhs = inv
    #         print(op, lhs, rhs)
            
    # do the same for daikon.
    for (key, inv_exprs) in datagen_info.daikon_sympy.items():
        datagen_proper_daikon[key] = []
        datagen_deleted_invs_daikon[key] = []
        for inv_expr in inv_exprs:
            op, lhs, rhs = inv_expr
            flag = True
            for data in nodatagen_info.data[key]:
                if not op(sympify(lhs, data), sympify(rhs, data)):
                    print(f"Invalid invariant: {inv_expr} for data point: {data}")
                    datagen_deleted_invs_daikon[key].append(inv_expr)
                    flag = False
                    break
            if flag:
                datagen_proper_daikon[key].append(inv_expr)
                
    # print("##### Final list of invariants produced by daikon:") 
    # for key in datagen_proper_daikon.keys():
    #     print(f"Key: {key}")
    #     for inv in datagen_proper_daikon[key]:
    #         op, lhs, rhs = inv
    #         print(op, lhs, rhs)
     
    print("----------- Finished processing datagen invariants -----------") 
    
    print("Validating nodatagen invariants") 
    #-------------- Nodatagen -------------------
    for (key, inv_exprs) in nodatagen_info.dig_sympy.items():
        nodata_proper_dig[key] = []
        nodata_deleted_invs_dig[key] = []
        for inv_expr in inv_exprs:
            op, lhs, rhs = inv_expr
            flag = True
            for data in datagen_info.data[key]:
                if not op(sympify(lhs, data), sympify(rhs, data)):
                    print(f"Invalid invariant: {inv_expr} for data point: {data}")
                    nodata_deleted_invs_dig[key].append(inv_expr)
                    flag = False
                    break
            if flag:
                nodata_proper_dig[key].append(inv_expr)
                
    # do the same for daikon.
    for (key, inv_exprs) in nodatagen_info.daikon_sympy.items():
        nodata_proper_daikon[key] = []
        nodata_deleted_invs_daikon[key] = []
        for inv_expr in inv_exprs:
            op, lhs, rhs = inv_expr
            flag = True
            for data in datagen_info.data[key]:
                if not op(sympify(lhs, data), sympify(rhs, data)):
                    print(f"Invalid invariant: {inv_expr} for data point: {data}")
                    nodata_deleted_invs_daikon[key].append(inv_expr)
                    flag = False
                    break
            if flag:
                nodata_proper_daikon[key].append(inv_expr)
    
    # print("##### Final list of invariants produced by dig:")
    # for key in nodata_proper_dig.keys():
    #     print(f"Key: {key}")
    #     for inv in nodata_proper_dig[key]:
    #         op, lhs, rhs = inv
    #         print(op, lhs, rhs)
            
    # print("##### Final list of invariants produced by daikon:")
    # for key in nodata_proper_daikon.keys():
    #     print(f"Key: {key}")
    #     for inv in nodata_proper_daikon[key]:
    #         op, lhs, rhs = inv
    #         print(op, lhs, rhs)
    
    # Dump everything in a BIG csv file.
    results = {
        'datagen_iterations': datagen_info.totaliterations,
        'nodatagen_iterations': nodatagen_info.totaliterations,
        'datagen_time': datagen_info.datagen_timetaken,
        'nodatagen_time': nodatagen_info.datagen_timetaken,
    }
    
    for key, values in datagen_info.dig_invariants_str.items():
        results[f'datagen_dig_total_{key}'] = len(values)
    for key, values in datagen_info.daikon_invariants_str.items():
        results[f'datagen_daikon_total_{key}'] = len(values)
        
    # for key, values in datagen_proper_dig.items():
    #     results[f'datagen_dig_proper_{key}'] = len(values)
    # for key, values in datagen_proper_daikon.items():
    #     results[f'datagen_daikon_proper_{key}'] = len(values)
        
    for key, values in datagen_deleted_invs_dig.items():
        results[f'datagen_dig_deleted_{key}'] = len(values)
    for key, values in datagen_deleted_invs_daikon.items():
        results[f'datagen_daikon_deleted_{key}'] = len(values)
   
    # NDG graphs     
    for key, values in nodatagen_info.dig_invariants_str.items():
        results[f'nodatagen_dig_total_{key}'] = len(values)
    for key, values in nodatagen_info.daikon_invariants_str.items():
        results[f'nodatagen_daikon_total_{key}'] = len(values)
    
    # for key, values in nodata_proper_dig.items():
    #     results[f'nodatagen_dig_proper_{key}'] = len(values)
    # for key, values in nodata_proper_daikon.items():
    #     results[f'nodatagen_daikon_proper_{key}'] = len(values)
    
    for key, values in nodata_deleted_invs_dig.items():
        results[f'nodatagen_dig_deleted_{key}'] = len(values)
    for key, values in nodata_deleted_invs_daikon.items():
        results[f'nodatagen_daikon_deleted_{key}'] = len(values)
    
    
    
    bigresults[benchname] = results
     
    # TODO: Generate smtlib expressions for the invariants, and check accuracy.
    
# Dump bigresults as a pandas dataframe.
res = pd.DataFrame(bigresults)
res.to_csv('results.csv')

with open("results.json", "w") as f:
    json.dump(bigresults, f, indent=4)