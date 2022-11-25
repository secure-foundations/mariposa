import random
from tqdm import tqdm
from path_utils import *
from wrap_utils import MODEL_TEST_GEN_ERROR

SMT_PLAIN_QLIST_PATH = "data/qlists/smtlib_all_plain_status.csv"
SMT_EXLUDE_QLIST_PATH = "data/qlists/smtlib_exclude"

def dump_smtlib_plain_status():
    file_paths = list_smt2_files(SMT_ALL_DIR)
    with open(SMT_PLAIN_QLIST_PATH, "w+") as out:
        for file_path in tqdm(file_paths):
            with open(file_path) as f:
                query = f.read()
                if "(set-info :status unsat)" in query:
                    out.write(file_path + ",unsat\n")
                elif "(set-info :status sat)" in query:
                    out.write(file_path + ",sat\n")
                else:
                    assert("(set-info :status unknown)" in query)
                    out.write(file_path + ",unknown\n")

def load_smlib_exclude_qlist():
    excludes = set()
    with open(SMT_EXLUDE_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip()
            excludes.add(line)
    return excludes

excludes = load_smlib_exclude_qlist()

def load_smtlib_qlist(status):
    filtered = []
    with open(SMT_PLAIN_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip().split(",")
            assert(len(line) == 2)
            if line[1] == status and line[0] not in excludes:
                filtered.append(line[0])
    return filtered

def load_random_smtlib_sat_qlist(count):
    file_paths = load_smtlib_qlist("sat")
    randlist = random.sample(file_paths, k=count)
    return randlist

def analyze_model_test():
    mdlt_count = 0
    mdltr_count = 0

    missing = 0
    failing = 0

    model_gen = {"unknown": 0, "timeout": 0, "ok": 0}
    test_gen = {MODEL_TEST_GEN_ERROR: 0}

    with open("data/qlists/smtlib_rand1K_sat") as f:
        for file_path in f.readlines():
            file_path = file_path.strip()
            mdl_path = to_model_path(file_path)
            mdlt_path = to_model_test_path(file_path)

            if not os.path.exists(mdlt_path):
                result = open(mdl_path).read().strip()
                model_gen[result] += 1
                continue

            if os.path.exists(mdl_path):
                model_gen["ok"] += 1

            if open(mdlt_path).read().strip() == MODEL_TEST_GEN_ERROR:
                test_gen[MODEL_TEST_GEN_ERROR] += 1
                continue

            mdlt_count += 1
            mdltr_path = to_model_test_res_path(file_path)

            if not os.path.exists(mdltr_path):
                missing += 1
                continue
            if open(mdltr_path).read() == "sat":
                mdltr_count += 1
            else:
                print(mdltr_path)
                failing += 1


    print(f"inital queries: {model_gen['ok'] + model_gen['unknown'] + model_gen['timeout']}")
    print(f"|model gen ok: {model_gen['ok']}")
    print(f"||tests gen ok: {mdlt_count}")
    print(f"| |passing: {mdltr_count}")
    print(f"| |missing: {missing}")
    print(f"| |failing: {failing}")
    print(f"||tests gen fail: {model_gen['ok'] - mdlt_count}")
    print(f"|model gen unknown: {model_gen['unknown']}")
    print(f"|model gen timeout: {model_gen['timeout']}")



if __name__ == "__main__":
    analyze_model_test()
    # dump_smtlib_plain_status()
    # load_random_smtlib_sat_qlist(1000)
    # for f in load_random_smtlib_sat_qlist(1000):
    #     print(f)
