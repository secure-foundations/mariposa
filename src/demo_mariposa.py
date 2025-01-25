import os, sys
from tabulate import tabulate
from tqdm import tqdm
import pandas as pd
from z3 import set_param

os.chdir("/home/yizhou7/mariposa")

from analysis.singleton_analyzer import SingletonAnalyzer
from base.factory import FACT
from base.exper import Experiment
from base.exper_analyzer import ExperAnalyzer
from debugger3 import Debugger3
from utils.system_utils import log_info
from benchmark_consts import *
from debugger.informed_editor import InformedEditor

queries = []

for query in UNSTABLE_MARIPOSA:
    dbg = Debugger3(query)
    st = dbg.get_status()
    if st["proofs"] == 0:
        continue
    queries.append(query)

for query in queries:
    print("./src/debugger3.py", "-i", query, "--create-singleton")
