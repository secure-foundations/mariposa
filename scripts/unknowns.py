from db_utils import *
from vbkv_filemap import *
import shutil

from plot_utils import *
import matplotlib.pyplot as plt
import multiprocessing as mp
from configer import Configer

c = Configer()

exp = c.load_known_experiment("opaque")
solver = c.load_known_solver("z3_4_12_2")

proj = c.load_known_project("d_lvbkv_closed")


table = load_sum_table(proj, solver, exp)
for row in table:
    stacked = np.hstack(row[2][:3,0])
    times = np.hstack(row[2][:3,1])
    # print(np.hstack(row[2][:3,0]).shape)
    uks = np.sum(stacked == RCode.UNKNOWN.value)
    uss = np.sum(stacked == RCode.UNSAT.value)
    if uks >= 10 and uss >= 10:
        print(row[0])
        print(uks, uss)
        print(np.mean(times[uks]) / 1000)
        print(np.mean(times[uss]) / 1000)
        print("")
