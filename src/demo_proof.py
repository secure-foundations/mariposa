import json
import os, sys
from tabulate import tabulate
from tqdm import tqdm
import pandas as pd
from z3 import set_param

from base.exper_analyzer import ExperAnalyzer
from debugger.edit_info import EditAction
from debugger.informed_editor import InformedEditor
from debugger.mutant_info import MutantInfo
from debugger3 import Debugger3
from utils.system_utils import log_info
from benchmark_consts import *
from debugger.file_builder import FileBuilder
from utils.analysis_utils import fmt_percent
from analysis.singleton_analyzer import SingletonAnalyzer

from debugger.proof_analyzer import ProofAnalyzer



p = ProofAnalyzer.from_proof_file("dbg/199ba4594c/proofs/reseed.3199813507728074554.proof")

