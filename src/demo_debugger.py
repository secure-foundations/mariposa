import sys
from debugger.demo_helper import *

query = sys.argv[1]

dbg = Debugger3(query)
st = dbg.get_status()

ba, fa = get_debug_status(dbg)
print(ba)

if isinstance(ba, SingletonAnalyzer):
    assert dbg.editor is not None
else:
    sys.exit(0)

assert isinstance(fa, str) or fa is None

tested, untested = check_tested(dbg, ba)

print(tabulate(tested, headers=["qname", "action", "result", "time", "query_path"]))