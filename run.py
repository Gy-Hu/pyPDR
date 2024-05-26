import argparse
import os
from datetime import datetime
from multiprocessing import Process
import sys
sys.path.append("..")
import model_encoder
import pdr
import time 
def run_with_limited_time(func, time):
    p = Process(target=func)
    p.start()
    p.join(time)
    if p.is_alive():
        p.terminate()
        return False
    return True


if __name__ == '__main__':
    #sys.stdout = open('file', 'w') #open this when we need the log
    help_info = "Usage: python main.py <file-name>.aag"
    parser = argparse.ArgumentParser(description="Run tests examples on the PDR algorithm")
    parser.add_argument('fileName', type=str, help='The name of the test to run', default=None, nargs='?')
    parser.add_argument('-m', type=int, help='the time limitation of one test to run', default=3600)
    parser.add_argument('-c', help='switch to counting time', action='store_true')
    #args = parser.parse_args(['/data/guangyuh/coding_env/pyPDR/dataset/aag4train/subset_0/nusmv.syncarb5^2.B.aag','-c']) #When you need to run single file, setup this
    args = parser.parse_args()
    if args.fileName is not None:
        file = args.fileName
        start_time = time.time()
        m = model_encoder.Model()
        end_time = time.time()
        parsing_time = end_time - start_time
        #print("============= Running test ===========")

        # Not using RL
        solver = pdr.PDR(*m.parse(file))
        startTime = datetime.now()
        solver.run()
        endTime = datetime.now()
        if args.c:
            print("TIME CONSUMING: " + str((endTime - startTime).seconds) + "seconds")
