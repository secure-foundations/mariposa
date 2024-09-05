import sys
from z3 import *
set_param(proof=True)

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
    return None
  assert p.num_args() == 1
  p = p.arg(0)
  assert is_app_of(p, Z3_OP_OR)
  l, r = p.arg(0), p.arg(1)
  assert is_app_of(l, Z3_OP_NOT)
  l = l.arg(0)
  assert is_quantifier(l)
  # print("(assert " + format_expr(r, 0) +")")
  return (l.qid(), r)

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

def is_quantifier_free(e):
  if is_const(e):
    return True
  if is_quantifier(e):
    return False
  for c in e.children():
    if not is_quantifier_free(c):
      return False
  return True

def get_assertion_qid(exp: z3.ExprRef):
  # TODO: nested
  if is_quantifier(exp):
    qid = exp.qid()
    # self.quants[qid] = exp
    return qid

  if is_app_of(exp, Z3_OP_IMPLIES):
    exp = exp.arg(1)
    if is_quantifier(exp):
      qid = exp.qid()
      return qid

    return None 

class Instantiater:
  def __init__(self, in_file_path, out_file_path):
    s = Solver()
    s.from_file(in_file_path)

    self.insts = dict()
    self.quants = dict()
    self.__visited = set()

    res = s.check()
    print(res)
    p = s.proof()
    self.match_qis(p)

    s2 = Solver()

    for a in s.assertions():
      qid = get_assertion_qid(a)

      if qid is not None:
        self.quants[qid] = a

    ranked = sorted(self.insts.items(),
                  key=lambda x: len(x[1]), reverse=True)

    handled = set()
    for qid, insts in ranked:
      if qid not in self.quants:
        print("unhandled", qid)
        continue
      q = self.quants[qid]
      # qf = is_quantifier_free(q.body())
      print(len(insts), qid)
      handled |= {qid}
      # if not qf:
      #   for inst in insts:
      #     print(inst)
      for inst in insts:
        s2.add(inst)

    for a in s.assertions():
      qid = get_assertion_qid(a)
      if qid in handled:
        print("handled", qid)
        continue
      s2.add(a)
      
    with open(out_file_path, "w") as f:
      f.write(s2.to_smt2())

  def match_qis(self, p):
    oid = p.get_id()
    if oid in self.__visited:
      return
    self.__visited.add(oid)

    if not is_app(p) or is_const(p):
      return

    if match_sk(p):
      return

    res = match_qi(p)
    if res is not None:
      qid, qi = res
      self.insts[qid] = self.insts.get(qid, set()) | {qi}
      return

    for c in p.children():
      self.match_qis(c)



if __name__ == "__main__":
  Instantiater(sys.argv[1], "out.smt2")
