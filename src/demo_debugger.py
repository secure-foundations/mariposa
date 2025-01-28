import json
from debugger.mutant_info import MutantInfo
from debugger3 import Debugger3
from debugger.quant_graph import TheirAnalysis, TheirParser

# query = "data/projs/vsystemsnew/base.z3/noderep-smt-spec__cyclicbuffer.3.smt2"
query = "data/projs/anvil/base.z3/zookeeper-smt-rabbitmq-smt-rabbitmq_controller__proof__liveness__resource_match.1.smt2"

# dbg = Debugger3(query)
# assert dbg.editor is not None

# mi = dbg.editor.trace
m_json = "dbg/eccd7ce2d9/meta/rename.7278557073235958777.json"
mi = MutantInfo.from_dict(json.load(open(m_json)))
mi.build_graph_log()
mi.build_stats_log()
ta = TheirAnalysis(TheirParser(mi.graph_path, mi.stats_path))

qname = "internal_rabbitmq_controller!rabbitmq_controller.model.resource.stateful_set.make_rabbitmq_pod_spec.?_definition"
scores = ta.compute_sub_ratios({qname})
# print(ta.name_to_qidxs)
for qname in scores:
    print(qname, scores[qname])

