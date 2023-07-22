'''
Main function to run BMC
'''
import subprocess
import argparse
import os, os.path, shutil
import sys
from pathlib import Path
import model
import bmc
import time
import argparse
import z3
import tempfile
import copy
from utils.formula import CNFFormula

def convert_aig_to_aag(file):
    aig_path = file
    with tempfile.TemporaryDirectory() as tmpdirname:
        aigtoaig_cmd='./aiger/aigtoaig'
        tmpdir = Path(tmpdirname)
        shutil.copy(aig_path, tmpdir)
        subprocess.call([aigtoaig_cmd, aig_path, tmpdir / "tmp.aag"])
        return bmc.BMC(*m.parse(tmpdir / "tmp.aag"))
        
def k_induction(bmc, args):
    # BASE CASE
    bmc_1 = copy.deepcopy(bmc)
    bmc_1.setup()
    bmc_1.add(z3.Not(bmc_1.post.cube()))
    if bmc_1.check() == z3.unsat:
        # INDUCTION STEP
        bmc.setup(induction=True) # for verify P & T -> P
        bmc_1.setup() # verify init & T -> P
        bmc.add(bmc.post.cube())
        bmc.slv.push(); bmc_1.slv.push()
        for step in range(1, args.k+1):
            bmc.slv.pop()
            print(f"Checking for CEX after {step} transitions")
            bmc.unroll()
            bmc.slv.push()
            bmc.add(z3.Not(bmc.post.cube()))
            if bmc.check() == z3.unsat:
                print(f"Verified, p is {step} inductive")
                return
            
            bmc_1.slv.pop()
            bmc_1.unroll()
            bmc_1.slv.push()
            bmc_1.add(z3.Not(bmc_1.post.cube()))
            if bmc_1.check() == z3.sat:
                print(f"Found CEX after {step} transitions")
                return
        print(f"Invariant couldn't be proven inductive after {args.k} transitions")
    else:
        print("Invariant doesn't hold and there is a counterexample")
        # Add your trace_print function call here if needed
        return
    
def bmc_main(bmc, args):
    for _ in range(1, args.k+1): 
        print(f"Unrolling k = {_}")
        bmc.unroll()
        # execute bmc.unroll() k times
        #for __ in range(34): bmc.unroll() #aig_benchmark/hwmcc07/intel/intel_038.aig -> idx = 35 (or 37, or other bound?)
        bmc.slv.push()
        bmc.add(z3.Not(bmc.post.cube()))
        if bmc.check() == z3.sat:
            print(f"SAT, k = {_}, idx = {bmc.cnt}")
            exit(0)
        else:
            bmc.slv.pop()
            
    # reach here means UNSAT, k = args.k
    print(f"The result is unknown after {args.k} bound by runing bmc")
    
def convert_z3_to_dimacs(z3_expr): # z3_expr is a z3 expression, e.g. bmc.slv.assertions()
    f = CNFFormula.from_z3(z3_expr)
    cnf_string_lst = f.to_dimacs_string()
    #print(cnf_string_lst)
    f.to_dimacs_file("tmp.cnf")

if __name__ == '__main__':
    help_info = "Usage: python main.py <file-name>.aag (or <file-name>.aig) --k <unrolling steps>"
    parser = argparse.ArgumentParser(description="Run tests examples on the BMC algorithm")
    parser.add_argument('--aag', type=str, help='The name of the test to run', default=None, nargs='?')
    parser.add_argument('--k', type=int, help='The number of unrolling steps', default=10, nargs='?')
    parser.add_argument('--mode', type=str, help='The mode of the algorithm, input bmc or k-ind', default='bmc', nargs='?')
    #args = parser.parse_args(['--aag', 'dataset/aig_benchmark/hwmcc07/intel/intel_038.aig', '--k', '100'])
    args = parser.parse_args(['--aag', 'cnt.aag', '--k', '100'])
    #args = parser.parse_args()
    m = model.Model()
    # UNSAFE 1 - simple
    #file = "dataset/aig_benchmark/hwmcc07_tip_aag/texas.ifetch1^8.E.aag"
    # UNSAFE 2 - toy
    #file = "dataset/aig_benchmark/hwmcc10-mod/shortp0.aag"
    # SAFE 1 - simple
    # file = "dataset/aig_benchmark/hwmcc07_tip/nusmv.syncarb5^2.B.aag"
    # SAFE 2 - toy
    # file = "./cnt.aag"

    file = args.aag
    if file.endswith(".aig"): 
        bmc = convert_aig_to_aag(file)
    else:
        bmc = bmc.BMC(*m.parse(file))

    bmc.setup()
    if args.mode == 'bmc':
        # bmc
        print("Now running bmc")
        bmc_main(bmc, args)
    elif args.mode == 'k-ind':
        # k-induction
        print("Now running k-induction")
        k_induction(bmc, args)

    