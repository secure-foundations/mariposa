import sys
import os
import subprocess

GLOBAL_RLIMIT = 30000000
GLOBAL_TIMOUT = 120
Z3_BIN_PATH = "z3"
MARIPOSA_BIN_PATH = "./target/release/mariposa"
MODEL_TEST_GEN_ERROR = "E_MDLT_G"

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
            f.write("unknown")
        elif "timeout" in model:
            f.write("timeout")
        else:
            f.write(parse_z3_model(model))

def z3_run_model_test(model_test_file, output_file):
    command = f"{Z3_BIN_PATH} {model_test_file} rlimit={GLOBAL_RLIMIT} -T:{GLOBAL_TIMOUT}"
    result = subprocess_run(command)
    if result.endswith("unsat"):
        assert(False)
    if result.endswith("sat"):
        with open(output_file, "w+") as f:
            f.write("sat")
    else:
        assert(False)

def mariposa_gen_model_test(query_file, model_file, output_file):
    command = f"{MARIPOSA_BIN_PATH} -i {query_file} -m {model_file} -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        os.system(f"echo {MODEL_TEST_GEN_ERROR} > {output_file}")
        print(f"model test gen failed: {output_file}, emiting an error file")

def main():
    option = sys.argv[1]
    if option  == "z3_get_model":
        z3_get_model(sys.argv[2], sys.argv[3])
    elif option == "z3_run_model_test":
        z3_run_model_test(sys.argv[2], sys.argv[3])
    elif option == "mariposa_gen_model_test":
        mariposa_gen_model_test(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        print("unknown wrap_util option " + option)

if __name__ == "__main__":
    main()

