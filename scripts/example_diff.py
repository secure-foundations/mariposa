import subprocess
import time

def subprocess_run(command, time_limit, debug=False, cwd=None):
    command = f"timeout {time_limit} " + command
    if debug:
        print(command)
    start_time = time.time()
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

queries = ["verified-secprop-conf_ni_entry.i.dfyImpl___module.__default.lemma__validEnclaveEx__conf.smt2", 
    "verified-sha-sha256-body-16-xx.gen.dfyCheckWellformed___module.__default.va__refined__Body__16__XX.smt2", 
    "verified-entry.i.dfyImpl___module.__default.lemma__userExecutionModel__sufficiency.smt2", 
    "verified-valesupp.i.dfyCheckWellformed___module.__default.va__get__osp.smt2", 
    "verified-secprop-sec_prop_util.i.dfyImpl___module.__default.lemma__user__regs__domain.smt2", 
    "verified-mapping.s.dfyCheckWellformed___module.__default.updateL2Pte.smt2"]

for query in queries:
    query = query.strip()
    print(query)
    # plain z3 queries
    command = f"solvers/z3-4.11.2 data/d_komodo_z3_clean/{query} -T:10"
    out, err, elapsed = subprocess_run(command, 11)
    assert "unsat" in out

    # z3 queries with no options
    command = f"solvers/z3-4.11.2 data/d_komodo_z3_no_opt/{query} -T:10"
    out, err, elapsed = subprocess_run(command, 11)
    assert "timeout" in out

    # z3 queries with only auto-config false
    command = f"solvers/z3-4.11.2 data/d_komodo_z3_auto_off/{query} -T:10"
    out, err, elapsed = subprocess_run(command, 11)
    assert "unsat" in out

    # cvc5 query with bv2int convert to bv2nat
    command = f"solvers/cvc5-1.0.3 data/d_komodo_cvc5_clean/{query} --tlimit=10000"
    out, err, elapsed = subprocess_run(command, 11)
    assert "timeout" in err
