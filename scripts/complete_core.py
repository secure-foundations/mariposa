from analyze_unsat_core import *
from diff_smt import *

# c = Configer()

for orgi_name in PAIRS.keys():
    if orgi_name != "fs_dice":
        continue
    mini_name = PAIRS[orgi_name]
    UC = c.load_known_experiment("min_asserts")
    OP = c.load_known_experiment("opaque")
    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)

    exp = OP if orgi_name == "d_lvbkv_closed" else UC
    items0, ps0, tally0 = load(orgi, exp)
    items1, ps1, tally1 = load(mini, UC)

    if orgi_name == "d_lvbkv_closed":
        for k, v in items0.items():
            items0[k] = set([hacky_convert_file_path(x) for x in v])
            tally0 = set([hacky_convert_file_path(x) for x in tally0])

    # print(len(tally1 - tally0))
    count = 0
    for query in tally0:
        if query in items0[Stability.UNSOLVABLE]:
            continue
        if query not in tally1:
            continue
        if query in items1[Stability.UNSOLVABLE]:
            for c in items0:
                if query in items0[c]:
                    print(c)
            print("cp " + orgi.clean_dir + "/" + query + " temp/woot.smt2")
            print("cp " + mini.clean_dir + "/" + query + " temp/core.smt2")
            count += 1
    break
    print(count / len(tally0))

# # os.system("./target/release/mariposa -i {} -o {}".format(orig, "temp/woot2.smt2"))

# orig_asserts = get_asserts(orig)
# mini_asserts = get_asserts(mini)

# for i in orig_asserts.keys() - mini_asserts.keys():
#     print(orig_asserts[i])



# diff2 = random.choices(diff, k=len(diff) // 2)
# print(diff1 == diff2)

# # print(i)