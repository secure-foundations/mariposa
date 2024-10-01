#!/usr/bin/env python3

from z3 import set_param
from debugger3 import Debugger3, make_iteration_dir
from query_editor import BasicQueryWriter


def demo0():
    query = "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2"
    temp_prefix = make_iteration_dir(query)

    dbg = Debugger3(query, False, True)
    dbg.debug_trace(temp_prefix + "report.v0.txt")

    w = dbg.get_editor()
    w.skolemize_qids(
        {
            "user_lib__spec__cyclicbuffer__log_entry_alive_wrap_around_51",
        }
    )
    w.write(temp_prefix + "v1.smt2")

    dbg = Debugger3(temp_prefix + "v1.smt2", False, True)
    dbg.debug_trace(temp_prefix + "report.v1.txt")
    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "prelude_eucmod",
        }
    )
    w.write(temp_prefix + "v2.smt2")


def demo1():
    query = "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2"
    temp_prefix = make_iteration_dir(query)
    dbg = Debugger3(query, False, True)
    dbg.debug_trace(temp_prefix + "report.v0.txt")
    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "user_vstd__set__axiom_set_ext_equal_101",
        }
    )
    w.banish_qids(
        {
            "user_vstd__std_specs__bits__axiom_u64_leading_zeros_44",
            # "internal_lib!page_organization.PageOrg.impl&__4.end_is_unused.?_definition",
        }
    )
    w.write(temp_prefix + "v1.smt2")

    w = BasicQueryWriter(temp_prefix + "v1.smt2")
    w.skolemize_qids({"user_vstd__set__axiom_set_ext_equal_100"})
    w.write(temp_prefix + "v2.smt2")

    w = BasicQueryWriter(temp_prefix + "v2.smt2")
    w.erase_qids({"user_vstd__set__axiom_set_ext_equal_100"})
    w.write(temp_prefix + "v3.smt2")

    # verus procedure:
    # Function-Def lib::segment::span_queue_delete
    # verus-mimalloc/segment.rs:333

    # query path:
    # gen/sproj_single_85d9af57e62fc7168f8e6ff9d694aa49163c62796635d0d42fcd8749b93f4356/split.smt2

    # alternative timeout: 10.0s
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  6.83 /  --           0.3
    # rename           61          0          0  6.66 /  --           0.12
    # reseed           61          0          0  6.70 /  --           0.12


def demo2():
    query = "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"
    temp_prefix = make_iteration_dir(query)

    dbg = Debugger3(query, False, True)
    dbg.debug_trace(temp_prefix + "report.v0.txt")

    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "user_vstd__set__axiom_set_ext_equal_101",
            "internal_vstd!set.impl&__0.subset_of.?_definition",
            "internal_vstd__set__Set<int.>_unbox_axiom_definition",
        }
    )
    w.banish_qids(
        {
            "user_vstd__std_specs__bits__axiom_u64_leading_zeros_44",
            "internal_lib!page_organization.PageOrg.impl&__4.end_is_unused.?_definition",
        }
    )
    w.write(temp_prefix + "v1.smt2")

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


if __name__ == "__main__":
    set_param(proof=True)
    demo0()
    demo1()
    demo2()
