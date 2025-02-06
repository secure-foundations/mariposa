from debugger.demo_utils import *
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger3 import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer
import math 
import multiprocessing
import z3

z3.set_param("proof", True)

# r = Reviewer2(q)
# report = r.get_report()
# indices = report.freq.loc[report.freq["qname"].isin(report.stabilized["qname"])].index
# report.freq["rank"] = report.freq["trace_count"].rank(method='min', ascending=False)
# print(report.freq.loc[indices]["rank"].min())
# # print(tabulate(report, headers='keys', tablefmt='psql'))

def get_collision_prob(k, n):
    return 100 * (1 - math.exp(-k*(k-1)/(2*n)))

# print(get_collision_prob(563685, 2**64))

def pre_analysis(q):
    r = Reviewer2(q)
    editor = r.editor
    skc = editor.proof.get_skolem_consequences()
    scores = dict()
    for qname, counter in skc.items():
        # print(qname, counter)
        scores[qname] = sum(counter.values())
    sorted_scores = sorted(scores, key=lambda x: scores[x], reverse=True)
    return sorted_scores[:2]

    # for qname in editor.list_qnames():
    #     if qname in editor.ignored:
    #         continue
    #     try:
    #         editor.debug_qanme(qname)
    #     except:
    #         continue

    # report = r.get_report()
    # print(tabulate(report.tested, headers='keys', tablefmt='psql'))
    
def do_edit(q, qname):
    r = Reviewer2(q)
    editor = r.editor
    # for qname in qnames:
    editor.edit_by_qname(qname, action=EditAction.SKOLEMIZE)
    skolem_path = "data/projs/bench_unstable.skolem/base.z3/" + r.name_hash + "." + qname  + ".smt2"
    editor.save(skolem_path)
    return skolem_path

def gen_proj(skolem_path):
    # os.system("rm -r data/projs/singleton_76af37b0a7.filtered data/projs/singleton_76af37b0a7 dbg/76af37b0a7")
    try:
        r = Reviewer2(skolem_path)
        return r.create_singleton_project()
    except:
        print("Failed to create project", skolem_path)
        pass
    return None

def run_proj(proj):
    print(f"./src/exper_wizard.py manager -e verify --total-parts 12 -i {proj} --clear")
    print(f"./src/analysis_wizard.py singleton -e verify -s z3_4_13_0 -i {proj}")
    filtered_proj = proj.replace("/base.z3", ".filtered/base.z3")
    print(f"python3 src/carve_and_rerun.py {filtered_proj}")

# def post_analysis():
#     r = Reviewer2("test.smt2")
#     report = r.get_report(True)
#     print(tabulate(report.tested, headers='keys', tablefmt='psql'))
#     print(tabulate(report.stabilized, headers='keys', tablefmt='psql'))

candidates = [
    "data/projs/bench_unstable/base.z3/d_fvbkv--lib-Marshalling-GenericMarshalling.i.dfy.Impl__GenericMarshalling.__default.MarshallByteArray.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--lib-Base-total_order_impl.i.dfy.Impl__Total__Order__Impl.__default.ArrayLargestLtPlus1.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--lib-Base-sequences.i.dfy.Impl__Sequences.__default.DisjointConcatenation.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--lib-Base-total_order_impl.i.dfy.Impl__Total__Order__Impl.__default.ArrayLargestLtePlus1.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--lib-Base-total_order_impl.i.dfy.Impl__Total__Order__Impl.__default.ArrayLargestLtePlus1.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--lib-Base-Sequences.i.dfy.Impl__Sequences.__default.DisjointConcatenation.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--Impl-JournalistImpl.i.dfy.Impl__JournalistImpl.Journalist.reallocJournalEntries.smt2",
    "data/projs/bench_unstable/base.z3/d_komodo--verified-smcapi.i.dfyImpl___module.__default.lemma__sha256__concat.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--Impl-JournalistModel.i.dfy.CheckWellformed__JournalistModel.__default.append.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--lib-Lang-LinearSequence.i.dfy.Impl__LinearSequence__i.__default.AllocAndMoveLseq.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--lib-Marshalling-GenericMarshalling.i.dfy.Impl__GenericMarshalling.__default.MarshallTupleContents.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--lib-Buckets-PackedStringArray.i.dfy.Impl__PackedStringArray.__default.UniqueRepr.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--Impl-CoordinationImpl.i.dfy.Impl__CoordinationImpl.__default.insert.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--Impl-JournalistMarshallingModel.i.dfy.Impl__JournalistMarshallingModel.__default.journalRangeFromHasChecksums.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--Impl-JournalistImpl.i.dfy.Impl__JournalistImpl.Journalist.freeze.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--lib-DataStructures-MutableBtreeBulkOperations.i.dfy.Impl__MutableBtreeBulkOperations.__default.ToSeqSubtree.smt2",
    "data/projs/bench_unstable/base.z3/d_lvbkv--Betree-BetreeInv.i.dfy.Impl__BetreeInv.__default.FlushPreservesLookups.smt2",
    "data/projs/bench_unstable/base.z3/d_fvbkv--Betree-BetreeInv.i.dfy.Impl__BetreeInv.__default.RedirectPreservesLookups.smt2",
]

# projs = []

# for q in candidates:
#     qnames = pre_analysis(q)
#     for qname in qnames:
#         skolem_path = do_edit(q, qname)
#         p = gen_proj(skolem_path)
#         if p is not None:
#             projs.append(p)
#         # post_analysis()

# print(projs)

projs = ['data/projs/singleton_3acddd81bc/base.z3', 'data/projs/singleton_7ad6c70163/base.z3', 'data/projs/singleton_bd12f47d44/base.z3', 'data/projs/singleton_26d6f273e1/base.z3', 'data/projs/singleton_21361a3ef8/base.z3', 'data/projs/singleton_268dfd496d/base.z3', 'data/projs/singleton_df4acc4ea9/base.z3', 'data/projs/singleton_42df1b9607/base.z3', 'data/projs/singleton_a180789acc/base.z3', 'data/projs/singleton_dd8d15c6bc/base.z3', 'data/projs/singleton_25648d1171/base.z3', 'data/projs/singleton_ea30e721e3/base.z3', 'data/projs/singleton_f5e3dc1afa/base.z3', 'data/projs/singleton_f8e6612949/base.z3', 'data/projs/singleton_fc6e849183/base.z3', 'data/projs/singleton_42a7ac0891/base.z3', 'data/projs/singleton_197a06a2a9/base.z3', 'data/projs/singleton_b3d9db0000/base.z3', 'data/projs/singleton_fdf6710d6d/base.z3', 'data/projs/singleton_7e554f6f24/base.z3', 'data/projs/singleton_9b1092fb35/base.z3', 'data/projs/singleton_fb07173727/base.z3', 'data/projs/singleton_de9d37e7ed/base.z3', 'data/projs/singleton_de18fce283/base.z3', 'data/projs/singleton_20a3ebfddb/base.z3', 'data/projs/singleton_4a9adfa7f1/base.z3', 'data/projs/singleton_921ee81f27/base.z3', 'data/projs/singleton_c4e73b3f59/base.z3', 'data/projs/singleton_6e7ccc989b/base.z3', 'data/projs/singleton_08a503a9af/base.z3', 'data/projs/singleton_1364fd2fcd/base.z3', 'data/projs/singleton_4e592fe422/base.z3', 'data/projs/singleton_b974f19f66/base.z3', 'data/projs/singleton_737c35b971/base.z3']

for proj in projs:
    run_proj(proj)

# q = "data/projs/vsystemsnew/base.z3/noderep-smt-spec__cyclicbuffer.3.smt2"
# q = candidates[3]
# # pre_analysis(q)
# do_edit(q, ["mariposa_qid_2371"])
# gen_proj()
# post_analysis()
