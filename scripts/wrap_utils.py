import sys
import os
import subprocess
from enum import auto
from strenum import StrEnum

GLOBAL_RLIMIT = 30000000
GLOBAL_TIMOUT = 120
Z3_BIN_PATH = "z3"
MARIPOSA_BIN_PATH = "./target/release/mariposa"

class RCode(StrEnum):
    Z3_MG_ETO = auto() # z3 model gen timeout
    Z3_MG_EUK = auto() # z3 model gen unknown
    Z3_MG_EUS = auto() # z3 model gen unsat

    MP_P_EP = auto() # mariposa parse panic
    # MP_MTG_PS = auto() # mariposa model test gen pass
    MP_MTG_EP = auto() # mariposa model test gen panic

    MP_MSTG_EP = auto() # mariposa model shuffle test gen panic
    MP_MNTG_EP = auto() # mariposa model normalize test gen panic

    Z3_MT_ETO = auto() # z3 model test timeout
    Z3_MT_EUS = auto() # z3 model test unsat
    Z3_MT_EUK = auto() # z3 model test unknown

    Z3_MT_PS = auto() # z3 model test pass (sat)

    def get_description(self):
        if self == RCode.Z3_MG_ETO:
            return "z3 model gen timeout"
        elif self == RCode.Z3_MG_EUK:
            return "z3 model gen unknown"
        elif self == RCode.Z3_MG_EUS:
            return "z3 model gen unsat"
        elif self == RCode.MP_P_EP:
            return "mariposa parse panic"
        elif self == RCode.MP_MTG_EP:
            return "mariposa model test gen panic"
        elif self == RCode.MP_MSTG_EP:
            return "mariposa model shuffle test gen panic"
        elif self == RCode.MP_MNTG_EP:
            return "mariposa model normalize test gen panic"
        elif self == RCode.Z3_MT_ETO:
            return "z3 model test timeout"
        elif self == RCode.Z3_MT_EUS:
            return "z3 model test unsat"
        elif self == RCode.Z3_MT_EUK:
            return "z3 model test unknown"
        elif self == RCode.Z3_MT_PS:
            return "z3 model test pass (sat)"
        else:
            assert(False)

RCodes = [e.value for e in RCode]

def check_input_error(file_path):
    content = open(file_path).read()
    if content in RCodes:
        return content
    else:
        return None 

def subprocess_run(command, cwd=None):
    print(command)
    output = subprocess.run(command, shell=True, stdout=subprocess.PIPE, cwd=cwd).stdout
    return output.decode("utf-8").strip()

CARD_START = ";; cardinality constraint:"
CARD_END = ";; -----------"

def parse_z3_model(model):
    # will (and should) fail when unsat
    start = model.index("(") + 1
    model = model[start:-1]
    lines = model.split("\n")
    results = []
    skip = False
    # skip the cardinality part
    for line in lines:
        if CARD_START in line:
            skip = True
        elif CARD_END in line:
            skip = False
        if not skip:
            results.append(line)
    return "\n".join(results)

# dumps the model into output_file
def z3_get_model(query_file, output_file):
    command = f"{Z3_BIN_PATH} {query_file} -model rlimit={GLOBAL_RLIMIT} -T:{GLOBAL_TIMOUT}"
    model = subprocess_run(command)
    with open(output_file, "w+") as f:
        if "unknown" in model:
            f.write(RCode.Z3_MG_EUK)
        elif "timeout" in model:
            f.write(RCode.Z3_MG_ETO)
        else:
            f.write(parse_z3_model(model))

def z3_run_model_test(model_test_file, output_file):
    error = check_input_error(model_test_file)
    if error != None:
        with open(output_file, "w+") as f:
            f.write(error)
        return
    command = f"{Z3_BIN_PATH} {model_test_file} rlimit={GLOBAL_RLIMIT} -T:{GLOBAL_TIMOUT}"
    result = subprocess_run(command)
    if result.endswith("unsat"):
        print(f"model gen unsat: {output_file}, emiting file with error code")
        f.write(RCode.Z3_MT_EUS)
    if result.endswith("sat"):
        open(output_file, "w+").write(RCode.Z3_MT_PS)
    elif "unknown" in result:
        open(output_file, "w+").write(RCode.Z3_MT_EUK)
    elif "timeout" in result:
        open(output_file, "w+").write(RCode.Z3_MT_ETO)
    else:
        assert(False)

def mariposa_gen_model_test(query_file, model_file, output_file):
    error = check_input_error(model_file)
    if error != None:
        with open(output_file, "w+") as f:
            f.write(error)
        return
    command = f"{MARIPOSA_BIN_PATH} -i {query_file} -m {model_file} -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        with open(output_file, "w+") as f:
            f.write(RCode.MP_MTG_EP)
        print(f"model test gen failed: {output_file}, emiting file with error code")

def mariposa_gen_shuffle_model_test(model_test_file, output_file):
    error = check_input_error(model_test_file)
    if error != None:
        with open(output_file, "w+") as f:
            f.write(error)
        return
    command = f"{MARIPOSA_BIN_PATH} -i {model_test_file} -p shuffle -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        with open(output_file, "w+") as f:
            f.write(RCode.MP_MSTG_EP)
        print(f"model shuffle test gen failed: {output_file}, emiting file with error code")

def mariposa_gen_normalize_model_test(model_test_file, output_file):
    error = check_input_error(model_test_file)
    if error != None:
        with open(output_file, "w+") as f:
            f.write(error)
        return
    command = f"{MARIPOSA_BIN_PATH} -i {model_test_file} -p normalize -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        with open(output_file, "w+") as f:
            f.write(RCode.MP_MSTG_EP)
        print(f"model normalize test gen failed: {output_file}, emiting file with error code")

def main():
    option = sys.argv[1]
    if option  == "z3_get_model":
        z3_get_model(sys.argv[2], sys.argv[3])
    elif option == "z3_run_model_test":
        z3_run_model_test(sys.argv[2], sys.argv[3])
    elif option == "mariposa_gen_model_test":
        mariposa_gen_model_test(sys.argv[2], sys.argv[3], sys.argv[4])
    elif option == "mariposa_gen_shuffle_model_test":
        mariposa_gen_shuffle_model_test(sys.argv[2], sys.argv[3])
    elif option == "mariposa_gen_normalize_model_test":
        mariposa_gen_normalize_model_test(sys.argv[2], sys.argv[3])
    else:
        print("unknown wrap_util option " + option)
        assert(False)

if __name__ == "__main__":
    main()

