import re
from typing import Dict, Set
import numpy as np

CID_PATTERN = re.compile(":named (mariposa_cid_(\d)+)")

SHAKE_MAX = 18446744073709551615

def parse_shake_log(log_path) -> Dict[str, int]:
    scores = dict()
    with open(log_path, "r") as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip().split(":")
            scores[line[1]] = int(line[0])
            if scores[line[1]] == SHAKE_MAX:
                scores[line[1]] = np.nan
    return scores

def load_query_cids(query_path) -> Dict[str, int]:
    cids = dict()
    for line in open(query_path, "r"):
        if not line.startswith("(assert"):
            continue
        m = re.search(CID_PATTERN, line)
        cid = str(m.group(1))
        cids[cid] = line.strip()
    return cids

def create_shake_query(base_path, out_path, scores, max_score):
    new_lines = []
    for line in open(base_path, "r"):
        if not line.startswith("(assert"):
            new_lines.append(line)
            continue

        m = re.search(CID_PATTERN, line)
        cid = str(m.group(1))

        if scores[cid] <= max_score:
            new_lines.append(line)

    with open(out_path, "w") as f:
        f.writelines(new_lines)

def create_shake_query_from_log(base_path, log_path, max_score, out_path):
    scores = parse_shake_log(log_path)
    create_shake_query(base_path, out_path, scores, max_score)

def debug_shake(input_query_path, core_query_path, input_log_path):
    scores = parse_shake_log(input_log_path)
    core_cids = load_query_cids(core_query_path)
    base_cids = load_query_cids(input_query_path)

    max_core_score = max([scores[cid] for cid in core_cids.keys()])
    max_base_score = max(scores.values())

    print(f"max base score: {max_base_score}")
    print(f"max core score: {max_core_score}")
    
    print("")

    base_levels = dict()
    for cid, score in scores.items():
        if score not in base_levels:
            base_levels[score] = 0
        base_levels[score] += 1

    core_levels = dict()

    for cid in core_cids:
        score = scores[cid]
        if score not in core_levels:
            core_levels[score] = 0
        core_levels[score] += 1

    missing = 0
    for level in sorted(base_levels):
        core_count = core_levels.get(level, 0)
        if np.isnan(level):
            missing = core_count
        print(f"layer {level}:\t{base_levels[level]}\t{core_count}")
    
    if missing == 0:
        return

    print("missing core: ", missing)

    for cid in core_cids:
        if np.isnan(scores[cid]):
            print(f"{cid}: {base_cids[cid]}")