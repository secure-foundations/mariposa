import sys
import os

sys.path.append("/home/yizhou7/mariposa/src")
os.chdir("/home/yizhou7/mariposa/")

from tabulate import tabulate
from utils.cache_utils import load_cache

import numpy as np
from statistics import mean, median
import pandas as pd
from pathlib import Path
import glob
import matplotlib.pyplot as plt

from debugger.proof_analyzer import ProofAnalyzer
from evaluator import Evaluator
from datetime import datetime




pd.set_option("display.max_rows", None)  # Show all rows

def get_name_hash(filename):
    import hashlib
    return hashlib.sha256(filename.encode()).hexdigest()[0:10]

def trace_then_proof_rank(row, trace_heuristic = None):
    if trace_heuristic == None:
        priority = 1 if (row["trace_count"] == 0) else 0
    else:
        priority = 1 if trace_heuristic(row) else 0
    return (priority, row["proof_count"])  # Lower priority first, then sort by trace_count (descending)

def proof_then_trace_rank(row):
    priority = 1 if (row["proof_count"] > 0) else 0
    return (priority, -row["trace_count"])  

def linear_proof_trace_rank(row, k1 = 1, k2 = 1):
    return k1 * row["proof_count"] - k2 * row["trace_count"]

def multi_proof_trace_rank(row, k = 1):
    if row["trace_count"] == 0:
        # I am approximating the 0 with 1/row["proof_count"]
        return  (row["proof_count"] ** 2)
    return row["proof_count"] / row["trace_count"]



# I tried a bunch of fancy heuristics and just sorting by proof_count seems 
# to be the best thing
def proof_count_rank(row):
    return row["proof_count"] 

#will attempt to do a smart proof count here, where I count the importance of things
def proof_inst_graph_rank(row, pa):
    quantifier_name = row["qname"]

    if row["proof_count"] == 0:
        return 0
    try:
        inst_info = pa.get_inst_info_under_qname(quantifier_name)
    except:
        print(f"Quantifier {quantifier_name} with proof count {row['proof_count']} did not exist in the instantiations!")
        return 0
    instantiations : List[NodeRef] = inst_info.get_all_insts()
    total_indegree = 0
    for inst in instantiations:
        inst_node = pa.lookup_node(inst)
        if inst_node.name == "or":
            children = inst_node.children
            for child in children:
                in_degree = pa.in_degree(child)
                total_indegree += in_degree
        elif inst_node.name == "app":
            in_degree = pa.in_degree(inst)
            total_indegree += in_degree

    return total_indegree


def calculate_rank(file_name, ranking_heuristic = "naive", parameter1 = None, parameter2 = None):   
    report = load_cache("../" + file_name)
    ranked_report = report.freq.copy()
    # print(ranked_report)

    if ranking_heuristic == "naive":
        ranked_report["rank"] = ranked_report["trace_count"].rank(method='min', ascending=False)
    elif ranking_heuristic == "trace_then_proof":
        ranked_report["rank"] = ranked_report.apply(trace_then_proof_rank, axis=1)
    elif ranking_heuristic == "proof_then_trace":
        ranked_report["rank"] = ranked_report.apply(proof_then_trace_rank, axis=1)
    elif ranking_heuristic == "proof_trace_linear":
        if isinstance(parameter1, int) and isinstance(parameter2, int):
            rank_proof_trace_linear_curried = lambda row : linear_proof_trace_rank(row, k1 = parameter1, k2 = parameter2)
            ranked_report["rank"] = ranked_report.apply(rank_proof_trace_linear_curried, axis=1)
        else:
            max_proof = ranked_report["proof_count"].max()
            max_trace = ranked_report["trace_count"].max()

            rank_proof_trace_linear_curried = lambda row : linear_proof_trace_rank(row, k1 = max_proof, k2 = max_trace)
            ranked_report["rank"] = ranked_report.apply(rank_proof_trace_linear_curried, axis=1)
    elif ranking_heuristic == "proof_trace_mult":
        if isinstance(parameter1, int):
            rank_proof_trace_mult_curried = lambda row : multi_proof_trace_rank(row, k = parameter1)
            ranked_report["rank"] = ranked_report.apply(rank_proof_trace_mult_curried, axis=1)
        else:
            ranked_report["rank"] = ranked_report.apply(multi_proof_trace_rank, axis=1)
    elif ranking_heuristic == "proof_count":
        ranked_report["rank"] = ranked_report.apply(proof_count_rank, axis=1)
    elif ranking_heuristic == "proof_inst_graph":
        e = Evaluator("dbg/" + file_name[6:-7])
        pa : ProofAnalyzer = e.editor.proof
        rank_proof_inst_graph_curried = lambda row: proof_inst_graph_rank(row, pa)
        ranked_report["rank"] = ranked_report.apply(rank_proof_inst_graph_curried, axis=1)
    else:
        raise NameError(f"We do not support the heuristic {ranking_heuristic}")
    
    ranked_report = ranked_report.sort_values(by="rank", ascending=False).reset_index(drop = "true")
    # print(ranked_report)
    # print(report.stabilized)
    ranked_report['position'] = ranked_report['rank'].rank(method='min', ascending=False).astype(int)
    indices = ranked_report.loc[ranked_report["qname"].isin(report.stabilized["qname"])].index
    min_rank =  ranked_report.loc[indices]["position"].min()
    # print(min_rank)

    return min_rank


def calculate_rankings(kw_parameters, queries = None):
    min_ranks = {}
    min_rankings = []


    if queries == None:
        queries = []

        # Open and read the 'fast_unknown.txt' file
        with open('/home/amarshah/mariposa/src/fast_unknown.txt', 'r') as file:
            for line in file:
                processed_line = line.strip()
                queries.append(processed_line)

    queries = [f"cache/{query}.report" for query in queries]

    for file in queries:
        print(file)
        min_rank = calculate_rank(file, **kw_parameters)#, parameter1=1, parameter2=1000)
        min_ranks[file] = min_rank
        min_rankings += [min_rank]


    ranks = np.array(min_rankings)

    print(min_rankings)
    print("Mean: ", mean(min_rankings))
    print("Median: ", median(min_rankings))
    print(np.where(ranks == 1)[0].shape[0], "would fix on first try")
    print(np.where(ranks <= 3)[0].shape[0], "would fix in 3 or fewer tries")
    print(np.where(ranks <= 10)[0].shape[0], "would fix in 10 or fewer tries")

    return min_rankings
    # return np.where(ranks <= 10)[0].shape[0]

def main():
    kw_parameters = {"ranking_heuristic": "proof_inst_graph"}
    calculate_rankings(kw_parameters)

    return min_rankings

    # x = [2 **i for i in range(-10, 15)]
    # y = []
    # # for k in x:
    # #     kw_parameters = {"ranking_heuristic": "proof_trace_linear", "parameter1" : k, "parameter2": 1}
    # #     mean = calculate_rankings(kw_parameters)
    # #     y.append(mean)

    

    # # # Create the scatter plot
    # # plt.scatter(x, y, color='blue', marker='o')

    # # # Set log scale
    # # # plt.yscale("log")  # Log scale for Y-axis
    # # plt.xscale("log")  # Log scale for X-axis (optional)

    # # # Add labels and title
    # # plt.xlabel("k")
    # # plt.ylabel("Number of times fix is in top 10 ranking")
    # # plt.title("Frequency of top 10 fixes for ranking k * proof_count + trace_count")

    # # # Save the figure
    # # plt.savefig("/home/amarshah/mariposa/figures/linear_proof_trace_analysis_log.png", dpi=300, bbox_inches='tight')

    # # # Show the plot (optional)
    # # plt.show()




if __name__ == "__main__":
    main()
