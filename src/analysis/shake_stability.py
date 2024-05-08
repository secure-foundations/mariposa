import multiprocessing

import numpy as np
from analysis.core_analyzer import CoreAnalyzer
from base.defs import MARIPOSA_GROUPS
from base.factory import FACT
from utils.analysis_utils import PartialCDF
from utils.cache_utils import *
from utils.plot_utils import GROUP_PLOT_META
from utils.query_utils import count_asserts
from matplotlib import pyplot as plt

def handle_core_stability_analysis():
    group = FACT.get_group("d_komodo")
    ca = CoreAnalyzer(group)
    ca.print_status()