import sys
import os
import subprocess
from enum import auto
from strenum import StrEnum

Z3_BIN_PATH = "/home/yizhou7/z3/build/z3"
MARIPOSA_BIN_PATH = "./target/release/mariposa"

class RCode(StrEnum):
    Z3_GM_ETO = auto() # z3 model gen timeout (error)
    Z3_GM_EU = auto() # z3 model gen unknown (error)
    # Z3_GM_EUS = auto() # z3 model gen unsat (error)

    Z3_R_TO = auto() # z3 run timeout
    Z3_R_S = auto() # z3 run sat
    Z3_R_US = auto() # z3 run unsat
    Z3_R_U = auto() # z3 run unknown

    MP_P_EP = auto() # mariposa parse panic (error)
    MP_GPT_EP = auto() # mariposa (model) plain test gen panic (error)
    MP_GST_EP = auto() # mariposa (model) shuffle test gen panic (error)
    MP_GNT_EP = auto() # mariposa (model) normalize test gen panic (error)

    MP_GSE_EP = auto() # mariposa shuffle experiment gen panic (error)
    MP_GNE_EP = auto() # mariposa normalize experiment gen panic (error)
    MP_GME_EP = auto() # mariposa mix experiment gen panic (error)

code_des = {RCode.Z3_GM_ETO: "z3 model gen timeout (error)",
    RCode.Z3_GM_EU: "z3 model gen unknown (error)",
    RCode.Z3_R_TO: "z3 run timeout",
    RCode.Z3_R_S: "z3 run sat",
    RCode.Z3_R_US: "z3 run unsat",
    RCode.Z3_R_U: "z3 run unknown",
    RCode.MP_P_EP: "mariposa parse panic (error)",
    RCode.MP_GPT_EP: "mariposa (model) plain test gen panic (error)",
    RCode.MP_GST_EP: "mariposa (model) shuffle test gen panic (error)",
    RCode.MP_GNT_EP: "mariposa (model) normalize test gen panic (error)",
    RCode.MP_GSE_EP: "mariposa shuffle experiment gen panic (error)",
    RCode.MP_GNE_EP: "mariposa normalize experiment gen panic (error)",
    RCode.MP_GME_EP: "mariposa mix experiment gen panic (error)"}

RCodes = [e.value for e in RCode]

def subprocess_run(command, cwd=None):
    print(command)
    output = subprocess.run(command, shell=True, stdout=subprocess.PIPE, cwd=cwd).stdout
    return output.decode("utf-8").strip()

def write_rcode(output_path, rcode):
    open(output_path, "w+").write(f"rcode,{rcode}\n")

def check_input_rcode(file_path, output_file):
    line = open(file_path).readline()
    if line.startswith("rcode,"):
        with open(output_file, "w+") as f:
            f.write(line)
        # propagate error then exit
        exit(0)

CARD_START = ";; cardinality constraint:"
CARD_END = ";; -----------"

def parse_z3_model(model):
    # will fail when unsat
    # maybe emit Z3_GM_EUS 
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
def z3_gen_model(query_file, output_file, timeout):
    command = f"{Z3_BIN_PATH} {query_file} -model -T:{timeout}"
    model = subprocess_run(command)
    if "unknown" in model:
        write_rcode(output_file, RCode.Z3_GM_EU)
    elif "timeout" in model:
        write_rcode(output_file, RCode.Z3_GM_ETO)
    else:
        open(output_file, "w+").write(parse_z3_model(model))

def parse_z3_output(result):
    lines = result.split("\n")
    code = None
    i = 0
    while code == None:
        line = lines[i]
        if line == "unsat":
            code = RCode.Z3_R_US
        elif line == "sat":
            code = RCode.Z3_R_S
        elif line == "unknown":
            code = RCode.Z3_R_U
        elif line == "timeout":
            code = RCode.Z3_R_TO
        i += 1

    output_lines = []
    assert(code != None)
    output_lines.append(f"rcode,{code}")

    while True:
        assert(i < len(lines))
        line = lines[i]
        if line.startswith("(:"):
            break
        i += 1

    while i < len(lines):
        line = lines[i]
        assert(line.startswith(" :") or line.startswith("(:"))
        if line.endswith(")"):
            line = line[2:-1]
        else:
            line = line[2::]
        line = line.split()
        output_lines.append(f"{line[0]},{line[1]}")
        i += 1
    assert(i == len(lines))
    return "\n".join(output_lines)

def z3_run(query_path, output_file, timeout):
    check_input_rcode(query_path, output_file)
    command = f"{Z3_BIN_PATH} {query_path} -T:{timeout} -st"
    result = subprocess_run(command)
    result = parse_z3_output(result)
    open(output_file, "w+").write(result)

# generate a test from the original query and a model
def mp_gen_plain_test(query_file, model_file, output_file):
    check_input_rcode(model_file, output_file)
    command = f"{MARIPOSA_BIN_PATH} -i {query_file} -m {model_file} -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        write_rcode(output_file, RCode.MP_GPT_EP)
        print(f"plain test gen failed: {output_file}, emiting file with error code")

# shuffle the file generated by mp_gen_plain_test
def mp_gen_shuffle_test(model_test_file, output_file):
    check_input_rcode(model_test_file, output_file)
    command = f"{MARIPOSA_BIN_PATH} -i {model_test_file} -p shuffle -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        write_rcode(output_file, RCode.MP_GST_EP)
        print(f"shuffle test gen failed: {output_file}, emiting file with error code")

# normalize the file generated by mp_gen_plain_test
def mp_gen_normalize_test(model_test_file, output_file):
    check_input_rcode(model_test_file, output_file)
    command = f"{MARIPOSA_BIN_PATH} -i {model_test_file} -p normalize -o {output_file}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        write_rcode(output_file, RCode.MP_GNT_EP)
        print(f"normalize test gen failed: {output_file}, emiting file with error code")

# this is based on the original query, no model needed
def mp_gen_shuffle_exp(query_file, output_file, seed):
    command = f"{MARIPOSA_BIN_PATH} -i {query_file} -p shuffle -o {output_file} -s {seed}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        write_rcode(output_file, RCode.MP_GSE_EP)
        print(f"shuffle exp gen failed: {output_file}, emiting file with error code")

# this is based on the original query, no model needed
def mp_gen_normalize_exp(query_file, output_file, seed):
    command = f"{MARIPOSA_BIN_PATH} -i {query_file} -p normalize -o {output_file} -s {seed}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        write_rcode(output_file, RCode.MP_GNE_EP)
        print(f"normalize exp gen failed: {output_file}, emiting file with error code")

# this is based on the original query, no model needed
def mp_gen_mix_exp(query_file, output_file, seed):
    command = f"{MARIPOSA_BIN_PATH} -i {query_file} -p mix -o {output_file} -s {seed}"
    print(command)
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    if result.returncode != 0:
        write_rcode(output_file, RCode.MP_GME_EP)
        print(f"mix exp gen failed: {output_file}, emiting file with error code")

if __name__ == "__main__":
    if sys.argv[1] in {"mp_gen_mix_exp", "mp_gen_normalize_exp", "mp_gen_shuffle_exp", "z3_run"}:
        args = "\",\"".join(sys.argv[2:-1])
        args = "\"" + args + "\"," + sys.argv[-1]
    else:
        args = "\",\"".join(sys.argv[2::])
        args = "\"" + args + "\"," 
    call = f'{sys.argv[1]} ({args})'
    eval(call)