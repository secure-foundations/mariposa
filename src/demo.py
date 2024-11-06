#!/usr/bin/env python3

import os
from z3 import set_param
from debugger.trace_analyzer import EditAction
from debugger3 import Debugger3
from proof_builder import QunatInstInfo
from query_editor import BasicQueryWriter
from random import sample

from utils.system_utils import subprocess_run

TEMP = "temp"


class VersionManager:
    def __init__(self, query_path):
        self.query_path = query_path
        self.version = 0
        base_name = os.path.basename(query_path)
        assert base_name.endswith(".smt2")
        base_name = base_name[:-5]
        self.temp_prefix = f"{TEMP}/{base_name}."

    def update_version(self):
        self.version += 1

    def get_report_path(self):
        return f"{self.temp_prefix}report.v{self.version}.txt"

    def get_next_query_path(self):
        return f"{self.temp_prefix}v{self.version+1}.smt2"

    def get_query_path(self):
        if self.version == 0:
            return self.query_path
        return f"{self.temp_prefix}v{self.version}.smt2"

    def save_report(self, report):
        with open(self.get_report_path(), "w") as f:
            f.write(report)

    def run_all_versions(self):
        for i in range(1, self.version):
            query_path = f"{self.temp_prefix}v{i}.smt2"
            r, _, t = subprocess_run(["./bin/z3-4.13.0", "-T:10", query_path])
            print(f"version {i}: {r} in {(t/1000):.2f}s")


def demo0():
    v = VersionManager(
        "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2"
    )

    dbg = Debugger3(v.get_query_path(), False, True)
    dbg.debug_trace(v.get_report_path())

    w = dbg.get_editor()
    w.skolemize_qids(
        {
            "user_lib__spec__cyclicbuffer__log_entry_alive_wrap_around_51",
        }
    )

    w.write(v.get_next_query_path())
    v.update_version()

    dbg = Debugger3(v.get_query_path(), False, True)
    dbg.debug_trace(v.get_report_path())

    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "prelude_eucmod",
        }
    )
    w.write(v.get_next_query_path())


def demo1():
    v = VersionManager(
        "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2"
    )

    dbg = Debugger3(v.get_query_path(), False, True)
    diff = dbg.get_differ()
    v.save_report(diff.get_report())

    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "prelude_unbox_box_int",
            "internal_vstd!set.impl&__0.subset_of.?_definition",
        }
    )
    w.erase_qids(
        {
            "prelude_u_clip",
        }
    )
    w.write(v.get_next_query_path())

    # alternative timeout: 10.0s
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  6.28 /  --           0.3
    # rename           61          0          0  6.02 /  --           0.08
    # reseed           61          0          0  6.22 /  --           0.33

    v.update_version()
    w.instantiate_qids(
        {
            "internal_lib!types.impl&__21.wf_main.?_definition",
        }
    )
    w.write(v.get_next_query_path())

    # alternative timeout: 10.0s
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           0          0         61  --  / 10.00             0
    # rename            0          0         61  --  / 10.00             0
    # reseed            0          0         61  --  / 10.00             0



def demo2():
    v = VersionManager(
        "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"
    )
    dbg = Debugger3(v.get_query_path(), False, True)
    v.save_report(dbg.get_report())

    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "user_vstd__set__axiom_set_ext_equal_101",
            # "internal_vstd!set.impl&__0.subset_of.?_definition",
        }
    )
    w.erase_qids(
        {
            "user_vstd__std_specs__bits__axiom_u64_leading_zeros_44",
            # "internal_core__option__Option_unbox_axiom_definition",
            # "internal_vstd__set__Set<int.>_box_axiom_definition",
            "internal_lib!page_organization.PageOrg.impl&__4.end_is_unused.?_definition",
        }
    )
    w.write(v.get_next_query_path())

    # verus procedure:
    # Function-Def lib::segment::segment_span_free
    # verus-mimalloc/segment.rs:1605

    # query path:
    # gen/sproj_single_f92ddf0fb9c7199e74168ed6c487284bb7934fb87b40a92fabb7347baa058b79/split.smt2

    # alternative timeout: 10.0s
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  7.14 /  --           0.47
    # rename           61          0          0  6.77 /  --           0.15
    # reseed           61          0          0  7.04 /  --           0.56


def demo3_0():
    v = VersionManager(
        "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"
    )
    dbg = Debugger3(v.get_query_path(), False, True)
    diff = dbg.get_differ()
    v.save_report(diff.get_report())

    erase_qids = {
        # "user_vstd__std_specs__bits__axiom_u64_leading_zeros_44",
        # "internal_lib!linked_list.StuffAgree.impl&__4.view.?_pre_post_definition",
        # "internal_lib!page_organization.DlistEntry./DlistEntry/prev_invariant_definition",
    }

    inst_qids = {
        "internal_vstd!set.impl&__0.subset_of.?_definition",
    }

    w = dbg.get_editor()
    w.erase_qids(erase_qids)
    w.instantiate_qids(inst_qids)
    w.write(v.get_next_query_path())

def demo3():
    # query = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_push_back.smt2"
    # v = VersionManager(query)
    v = VersionManager(
        "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"
    )
    dbg = Debugger3(v.get_query_path(), False, True)
    diff = dbg.get_differ()
    v.save_report(diff.get_report())

    erase_qids = {
        "internal_lib!linked_list.StuffAgree.impl&__4.view.?_pre_post_definition",
        "internal_lib!page_organization.DlistEntry./DlistEntry/prev_invariant_definition",
    }

    inst_qids = {
        "internal_vstd!set.impl&__0.subset_of.?_definition",
    }

    w = dbg.get_editor()

    actions = diff.get_actions()
    # w.instantiate_qids({qid})
    # w.write(v.get_next_query_path())

    for _ in range(30):
        edits = sample(actions.keys(), 3)
        erase_qids = set()
        inst_qids = set()

        for qid in edits:
            if actions[qid] == EditAction.ERASE:
                erase_qids.add(qid)
            else:
                assert actions[qid] == EditAction.INSTANTIATE
                inst_qids.add(qid)

        w.erase_qids(erase_qids)
        w.instantiate_qids(inst_qids)

        w.write(v.get_next_query_path())
        v.update_version()
    v.run_all_versions()


def demo4():
    v = VersionManager("data/projs/v_systems/base.z3/ironsht--delegation_map_v.35.smt2")
    dbg = Debugger3(v.get_query_path(), False, False)
    diff = dbg.get_differ()
    # w = dbg.get_editor()
    # w.instantiate_qids({
    #     "prelude_unbox_box_bool",
    # })
    v.save_report(diff.get_report())
    w = dbg.get_editor()
    w.instantiate_qids({"internal_vstd!seq.Seq.len.?_pre_post_definition"})
    w.write(v.get_next_query_path())

    # for binding in qi.bindings:
    #     for i, v in binding.items():
    #         print(v, diff.pi.tt.defs[v])
    #         # print(v, diff.pi.tt.expand_def(v))
    # w.write(v.get_next_query_path())

if __name__ == "__main__":
    set_param(proof=True)
    # demo0()
    # demo1()
    # demo2()
    demo3_0()
    # demo4()
