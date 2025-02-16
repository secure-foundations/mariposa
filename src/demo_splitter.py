from base.exper_analyzer import ExperAnalyzer
from base.factory import FACT
from base.query_analyzer import Stability as STB
from utils.analysis_utils import Categorizer
from benchmark_consts import *
import numpy as np

SOLVER = FACT.get_solver("z3_4_13_0")
QUICK_CFG = FACT.get_config("verus_quick")
QA = FACT.get_analyzer("10sec")

stabilized = []


missed = {
    "data/projs/anvil/base.z3/zookeeper-smt-rabbitmq-smt-rabbitmq_controller__proof__liveness__resource_match__lemma_from_after_get_resource_step_to_after_update_resource_step.smt2",
    "data/projs/flowcert/base.z3/permission.14.smt2",
    "data/projs/vsystemsnew/base.z3/noderep-smt-spec__cyclicbuffer.3.smt2",
    "data/projs/vsystemsnew/base.z3/noderep-smt-spec__cyclicbuffer.5.smt2",
    "data/projs/verismo.dedup/base.z3/arch__ptram__ptram_p2.smt2",
    "data/projs/vsystemsnew/base.z3/mimalloc-smt-page_organization__PageOrg__impl_%4__merge_with_before_ll_inv_valid_unused.smt2",
    "data/projs/vsystemsnew/base.z3/page-table-smt-impl_u__l2_refinement.4.smt2",
    "data/projs/atmosphere/base.z3/kernel__create_and_share_pages.5.smt2",
}


goal_counts = []

for query in UNSTABLE_10_SECS:
    base_hash = get_name_hash(query)
    p_path = f"data/projs/splitter_{base_hash}/base.z3"
    p_split = FACT.get_project_by_path(p_path)
    e_split = FACT.try_get_exper(p_split, QUICK_CFG, SOLVER)
    fa = ExperAnalyzer(e_split, QA)
    sts = fa.stability_categories

    goal_count = len(sts[STB.STABLE]) + len(sts[STB.UNSTABLE]) + len(sts[STB.UNSOLVABLE])
    assert goal_count != 0

    if len(sts[STB.STABLE]) == goal_count:
        stabilized.append(query)
        # print(query)
    elif query in missed:
        print(query)
        print(len(sts[STB.UNSTABLE]), len(sts[STB.UNSOLVABLE]), goal_count)
    # print(goal_count)
    goal_counts.append(goal_count)

print(np.median(goal_counts))

# print((set(stabilized) -missed)))
# print(len(stabilized))

# print(len(query))

# print(len(sts[STB.STABLE]))
# print(len(sts[STB.UNSTABLE]))
    # print(len(sts[STB.UNSOLVABLE]))
    # print("")

    # print(len(sts[STB.STABLE]), len(sts[STB.UNSTABLE]), len(sts[STB.UNSOLVABLE]))
    # os.system("python3 src/analysis_wizard.py basic -e verus_quick -s z3_4_13_0 -i " + p_path)

