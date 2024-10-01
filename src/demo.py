#!/usr/bin/env python3

from z3 import set_param
from debugger3 import Debugger3, make_iteration_dir
from query_editor import BasicQueryWriter


def demo0():
    query = "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2"
    temp_dir = make_iteration_dir(query)

    dbg = Debugger3(query, False, True)
    dbg.debug_trace(temp_dir + "query.report.v0.txt")

    w = dbg.get_editor()
    w.skolemize_qids(
        {
            "user_lib__spec__cyclicbuffer__log_entry_alive_wrap_around_51",
        }
    )
    w.write(temp_dir + "v1.smt2")

    dbg = Debugger3(temp_dir + "query.v1.smt2", False, True)
    dbg.debug_trace(temp_dir + "report.v1.txt")
    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "prelude_eucmod",
        }
    )
    w.write(temp_dir + "v2.smt2")


def demo1():
    query = "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"
    temp_dir = make_iteration_dir(query)

    dbg = Debugger3(query, False, True)
    dbg.debug_trace(temp_dir + "report.v0.txt")

    w = dbg.get_editor()
    w.instantiate_qids(
        {
            "user_vstd__set__axiom_set_ext_equal_101",
        }
    )
    w.banish_qids(
        {
            "user_vstd__std_specs__bits__axiom_u64_leading_zeros_44",
            "internal_lib!page_organization.PageOrg.impl&__4.end_is_unused.?_definition",
        }
    )
    w.write(temp_dir + "v1.smt2")

    w = BasicQueryWriter(temp_dir + "v1.smt2")
    w.skolemize_qids(
        {
            "user_vstd__set__axiom_set_ext_equal_100",
            "user_vstd__set__axiom_set_ext_equal_100_1",
            "user_vstd__set__axiom_set_ext_equal_100_2",
            "user_vstd__set__axiom_set_ext_equal_100_3",
            "user_vstd__set__axiom_set_ext_equal_100_4",
        }
    )
    w.write(temp_dir + "v2.smt2")

    w = BasicQueryWriter(temp_dir + "v2.smt2")
    w.erase_qids(
        {
            "user_vstd__set__axiom_set_ext_equal_100",
            "user_vstd__set__axiom_set_ext_equal_100_1",
            "user_vstd__set__axiom_set_ext_equal_100_2",
            "user_vstd__set__axiom_set_ext_equal_100_3",
            "user_vstd__set__axiom_set_ext_equal_100_4",
        }
    )
    w.write(temp_dir + "v3.smt2")


if __name__ == "__main__":
    set_param(proof=True)
    # demo0()
    demo1()
