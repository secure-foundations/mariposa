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

def format_expr(e, depth):
  if is_const(e):
    return str(e)
    return

  name = e.decl().name()
  items = []
  prefix = " " * (depth + 1)
  for i in e.children():
    items += [format_expr(i, depth + 1)]
  length = sum([len(i) for i in items]) + len(name)
  if length > 80:
    items = [prefix + i for i in items]
    items = "(" + name + "\n" + "\n".join(items) + ")"
  else:
    items = "(" + name + " " + " ".join(items) + ")"
  return items

def match_qi(p):
  if p.decl().name() != "quant-inst":
    return False
  assert p.num_args() == 1
  p = p.arg(0)
  assert is_app_of(p, Z3_OP_OR)
  l, r = p.arg(0), p.arg(1)
  assert is_app_of(l, Z3_OP_NOT)
  l = l.arg(0)
  assert is_quantifier(l)

  # print(l.qid())
  # print("(assert " + format_expr(r, 0) +")")

  return True

def match_sk(p):
  if p.decl().name() != "sk":
    return False
  assert p.num_args() == 1
  p = p.arg(0)
  assert is_app_of(p, Z3_OP_OEQ)
  l, r = p.arg(0), p.arg(1)
  assert is_app_of(l, Z3_OP_NOT)
  l = l.arg(0)
  assert is_quantifier(l)
  print(l.skolem_id())
  # print(format_expr(r, 0))
  return True

def match_qis(p, visited):
  global count
  oid = p.get_id()

  if oid in visited:
    return
  
  visited.add(oid)

  if not is_app(p) or is_const(p):
    return

  if match_sk(p):
    return

  if match_qi(p):
    count += 1
    return

  for i in p.children():
    match_qis(i, visited)

v = set()
# print(p)
match_qis(p, v)
# print(len(v))
# print(count)
