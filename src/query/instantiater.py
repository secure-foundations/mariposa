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
  def __init__(self, in_file_path, seed):
    self.proc_solver = Solver()
    self.solver_opts = []

    if seed is not None:
      self.proc_solver.set("random_seed", seed)

    self.proc_solver.set("timeout", 30000)

    with open(in_file_path, "r") as f:
      for line in f.readlines():
        if line.startswith("(set-option"):
          self.solver_opts.append(line)

    self.proc_solver.from_file(in_file_path)

    # map qid to its assertion (incomplete)
    self.handled_quants = dict()

    for a in self.proc_solver.assertions():
      qid = get_assertion_qid(a)
      if qid is not None:
        self.handled_quants[qid] = a

    # map qid to its quant-inst applications
    self.insts = dict()
    self.__visited = set()

    self.inst_freq = []

  def process(self):
    res = self.proc_solver.check()

    if res != unsat:
      return False

    p = self.proc_solver.proof()
    self.match_qis(p)

    self.inst_freq = dict(map(lambda x: (x[0], len(x[1])),
                    self.insts.items()))

    # self.inst_freq = sorted(inst_freq, key=lambda x: x[1], reverse=True)
    return True

  def print_report(self):
    for qid, count in self.inst_freq:
      # q = self.quants[qid]
      # qf = is_quantifier_free(q.body())
      print(count, qid, end=" ")
      if qid not in self.handled_quants:
        print("(unhandled)")
        continue
      print("")

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
      # if not is_quantifier_free(qi):
      #   print(qid)
      #   print(qi)
      self.insts[qid] = self.insts.get(qid, set()) | {qi}
      return

    for c in p.children():
      self.match_qis(c)

  def output(self, out_file_path):
    out_solver = Solver()

    replaced = set()
    added = 0

    for qid, count in self.inst_freq:
      if qid not in self.handled_quants:
        continue
      added += count
      replaced |= {qid}

      for inst in self.insts[qid]:
        out_solver.add(inst)
        # print(format_expr(inst, 0))

    for a in self.proc_solver.assertions():
      qid = get_assertion_qid(a)
      # if qid in replaced:
      #   print("replaced", qid)
      #   continue
      out_solver.add(a)

    # print("replaced", len(replaced), "assertions")
    print("added", added, "assertions")
    
    with open(out_file_path, "w") as f:
      for opt in self.solver_opts:
        f.write(opt)
      f.write(out_solver.to_smt2())

# if __name__ == "__main__":
#   i = Instantiater(sys.argv[1])
#   i.print_report()
#   i.output(sys.argv[2])
