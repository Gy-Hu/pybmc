'''
Main function to run BMC
'''






import argparse
import os
os.environ["CUDA_VISIBLE_DEVICES"] = "1"
from datetime import datetime
from datetime import timedelta
from multiprocessing import Process
from threading import Thread

from time import sleep
import sys
sys.path.append("..")
import model
import bmc
import time
import argparse
import z3


#TODO: add a switch to open "generate training set or not"
if __name__ == '__main__':
    help_info = "Usage: python main.py <file-name>.aag"
    parser = argparse.ArgumentParser(description="Run tests examples on the PDR algorithm")
    parser.add_argument('--aag', type=str, help='The name of the test to run', default=None, nargs='?')
    parser.add_argument('--k', type=int, help='The number of unrolling steps', default=10, nargs='?')
    args = parser.parse_args()
    m = model.Model()
    # SAT 1 - simple
    #file = "/data/guangyuh/coding_env/pybmc/dataset/aig_benchmark/hwmcc07_tip_aag/texas.ifetch1^8.E.aag"
    # SAT 2 - toy
    #file = "/data/guangyuh/coding_env/pybmc/dataset/aig_benchmark/hwmcc10-mod/shortp0.aag"
    # UNSAT 1 - toy
    # file = "/data/guangyuh/coding_env/pybmc/dataset/aig_benchmark/hwmcc07_tip/nusmv.syncarb5^2.B.aag"

    file = args.aag
    prev_fidx = 0
    bmc = bmc.BMC(*m.parse(file))

    bmc.setup()

    for _ in range(1, args.k): 
        print(f"Unrolling k = {_}")
        bmc.unroll()
        bmc.slv.push()
        bmc.add(z3.Not(bmc.post.cube()))
        if bmc.check() == z3.sat:
            print(f"SAT, k = {_}")
            exit(0)
        else:
            bmc.slv.pop()

    # reach here means UNSAT, k = args.k
    print(f"The result is unknown after k {args.k} bound")