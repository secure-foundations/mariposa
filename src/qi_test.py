from z3 import *
set_param(proof=True)

print(get_version_string())
s = Solver()
s.from_file("woot2.smt2")

# e: z3.z3.ExprRef
res = s.check()
print(res)
p = s.proof()
count = 0

def match_qi(p):
  if p.decl().name() != "quant-inst":
    return False
  p = p.arg(0)
  assert is_app_of(p, Z3_OP_OR)
  l, r = p.arg(0), p.arg(1)
  assert is_app_of(l, Z3_OP_NOT)
  l = l.arg(0)
  assert isinstance(l, QuantifierRef)

  return True

def print_qis(p, visited):
  global count
  oid = p.get_id()

  if oid in visited:
    return
  
  visited.add(oid)

  if not is_app(p):
    return

  if match_qi(p):
    count += 1
    return

  for i in p.children():
    print_qis(i, visited)

v = set()

print_qis(p, v)
print(len(v))
print(count)
