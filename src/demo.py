#!/usr/bin/env python3

import os, sys
from z3 import set_param
from base.solver import RCode
from debugger.quant_graph import QuantGraph
from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3
from random import sample
from demos.unstable2 import *
from demos.unstable4 import *
from demos.unstable7 import *
from demos.unsolvable1 import *
from demos.unsolvable2 import *
from demos.unsolvable3 import *
from demos.unsolvable5 import *
from demos.unsolvable6 import *

from utils.system_utils import log_info, subprocess_run

ITER = "dbg/iters"


def copy_to_iter_dir(src_path):
    items = src_path.split("/")
    assert items[2] == "edits"
    base = items[1]
    assert base.endswith(".smt2")
    new_name = f"{base[:-5]}.{items[3]}"
    new_path = f"{ITER}/{new_name}"
    # print(new_path)
    if not os.path.exists(ITER):
        os.mkdir(ITER)
    subprocess_run(["cp", src_path, new_path])
    log_info(f"[iter] copied to {new_path}")
    return new_path


def test0(q):
    dbg = Debugger3(q, clear_edits=False)
    # dbg.try_random_edits()
    # dbg.make_single_edits_project()
    dbg.test_edit_with_id(8788092644892)


def unstable1(q):
    # this is an example where z3 gives up too early
    dbg = Debugger3(q)

    # dbg.try_random_edits()
    # dbg.try_ranked_edits()

    edit_ids = {
        "user_lib__spec__cyclicbuffer__log_entry_alive_wrap_around_51",
    }
    # time to unsat: 0.03
    # dbg/noderep--spec__cyclicbuffer.3.smt2/edits/v1.smt2

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          49         12          0  0.06 / 0.03          0.09
    # rename           61          0          0  0.03 /  --           0
    # reseed           61          0          0  0.04 /  --           0

    dbg.test_edit(edit_ids)


def unstable3(q):
    # FIXME: this report makes no sense
    dbg = Debugger3(q, False)

    dbg.print_status()
    dbg.try_ranked_edits()


def unstable5(q):
    pass


def unstable6(q):
    # FIXME: fail to build proof
    dbg = Debugger3(q, True, False)
    dbg.try_ranked_edits()


# def anvil1():
#     q = "data/projs/anvil/base.z3/rabbitmq-log-rabbitmq_controller__proof__helper_invariants__validation__lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable.smt2"
#     dbg = Debugger3(q, overwrite_reports=False)

#     # dbg.test_edit({
#     #     "internal_rabbitmq_controller!kubernetes_api_objects.spec.dynamic.DynamicObjectView./DynamicObjectView_constructor_definition": EditAction.INSTANTIATE,
#     # })


QUERIES = {
    "test0": "data/projs/v_systems/base.z3/ironsht--delegation_map_v.35.smt2",

    # "unstable1": "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2",
    "unstable2": "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg__impl__4__take_page_from_unused_queue_ll_inv_valid_unused.smt2",
    # "unstable3": "data/projs/v_systems/base.z3/mimalloc--commit_segment.1.smt2",
    "unstable4": "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg.69.smt2",
    # "unstable5": "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.5.smt2",
    # "unstable6": "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg__impl__4__merge_with_before_ll_inv_valid_unused.smt2",
    "unstable7": "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2",

    "unsolvable1": "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2",
    "unsolvable2": "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free_coalesce_before.smt2",
    "unsolvable3": "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_push_back.smt2",

    "unsolvable5": "data/projs/v_systems/base.z3/mimalloc--segment.1.smt2",
    "unsolvable5_30": "test_30.smt2",

    "unsolvable6": "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_remove.smt2",
    "unsolvable6_34": "test_34.smt2",
}

    # q = queries[name]
    # eval(name)(q)

    # dbg = Debugger3("test_30.smt2", clear_edits=False)
    # dbg.make_single_edits_project()
    # name = dbg.get_project_name("single_edits")

    # print(f"./src/exper_wizard.py manager -e verus_verify --total-parts 10 -s z3_4_13_0 --clear-existing -i data/projs/{name}/base.z3")
    # print(f"./src/analysis_wizard.py veri-verus -e verus_verify -s z3_4_13_0 -i data/projs/{name}/base.z3")
    # print(f"./src/exper_wizard.py data-sync -i data/projs/{name}_filtered/base.z3 --clear")
    # print(f"./src/exper_wizard.py manager -e verus_quick --total-parts 10 -s z3_4_13_0 --clear-existing -i data/projs/{name}_filtered/base.z3")
    # print(f"./src/analysis_wizard.py basic -e verus_quick -s z3_4_13_0 -i data/projs/{name}_filtered/base.z3")

def foo():
    set_param(proof=True)
    name = sys.argv[1]
    query = QUERIES[name]
    dbg = Debugger3(query)
    
    qids = []

    for hid in eval(name + "()"):
        ei = dbg.test_edit_with_id(hid)
        assert len(ei.edit) == 1
        qid = list(ei.edit.keys())[0]
        qids.append(qid)
    
    dbg.differ.do_stuff(qids)

    #     if not dbg.differ.is_root(qid):
    #         rid = dbg.differ.get_root(qid)
    #     else:
    #         rid = qid

    #     group_total = 0

    #     for qid in dbg.differ.trace_freq[rid]:
    #         if qid not in dbg.rank:
    #             continue

    #         group_total += dbg.rank[qid][1]

    #     rk = 0

    #     for k, (_, v) in dbg.rank.items():
    #         # print(k, v)
    #         if group_total >= v:
    #             break
    #         rk += 1

    #     print(f"{rid}")
    #     print(rk, round(group_total))

        # print(f"{qid} {dbg.rank[qid][0]}/{total}")

if __name__ == "__main__":
    foo()