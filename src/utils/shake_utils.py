import re
from typing import Dict, Set

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
                scores[line[1]] = -1
    return scores

def load_query_cids(query_path) -> Set[str]:
    cids = set()
    for line in open(query_path, "r"):
        if not line.startswith("(assert"):
            continue
        m = re.search(CID_PATTERN, line)
        cid = str(m.group(1))
        cids.add(cid)
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
