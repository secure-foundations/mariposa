ASSERT_LABELS = ["qfree", "others", "prelude", "type", "heap", "goal"]
NON_GOAL_LABELS = ["qfree", "others", "prelude", "type", "heap"]

import re

DFY_QID_PAT = re.compile(r"qid \|([^\|])*\|")

def get_dfy_assert_label(line):
    if not line.startswith("(assert"):
        return None
    
    if line.startswith("(assert (not (=>") or  \
        line.startswith("(assert (not (let"):
        return "goal"

    qid = re.search(DFY_QID_PAT, line)
    if qid is None:
        if "forall" in line:
            return "others"
        else:
            return "qfree"
    qid = qid.group(0)

    if "DafnyPre" in qid:
        return "prelude"
    elif "funType" in qid:
        return "type"
    elif "Heap" in line:
        return "heap"
    else:
        return "others"

# def add_back_dfy_asserts(label, origi_file, mini_file, out_file):
#     assert label in ASSERT_LABELS
#     adding = set()
#     for line in open(origi_file, "r").readlines():
#         if get_dfy_assert_label(line) == label:
#             adding.add(line)
#     out_file = open(out_file, "w")
#     for line in open(mini_file, "r").readlines():
#         if line in adding:
#             continue
#         if line.startswith("(check-sat)"):
#             out_file.write("".join(adding))
#             out_file.write(line)
#             break
#         out_file.write(line)

# def get_dfy_asserts(file):
#     f = open(file, "r")
#     lines = f.readlines()
#     labels = {k: 0 for k in ASSERT_LABELS}

#     for line in lines:
#         line = line.strip()
#         label = get_dfy_assert_label(line)
#         if label is not None:
#             labels[label] += 1
#     return labels

# for label in NON_GOAL_LABELS:
#     if os.path.exists(f"data/d_fvbkv_asserts/{label}"):
#         continue
#     os.mkdir(f"data/d_fvbkv_asserts/{label}") 

#     for query in stabilized:
#         orgi_path = orgi.clean_dir + "/" + query
#         # if not os.path.exists(orgi_path):
#         #     orgi_path = orgi_path.replace("dfy.", "dfyxxx")
#         # if not os.path.exists(orgi_path):
#         #     orgi_path = orgi_path.replace(".smt2", ".1.smt2")
#         mini_path = mini.clean_dir + "/" + query
#         out_path = f"data/d_fvbkv_asserts/{label}/{query}"
#         add_back_dfy_asserts(label, orgi_path, mini_path, out_path)

# def print_asserts(orgi_name, mini_name):
#     _, _, keep = get_basic_keep(orgi_name, mini_name)
#     orgi = c.load_known_project(orgi_name)
#     mini = c.load_known_project(mini_name)

#     pts0 = []
#     pts1 = []
#     for query in tqdm(keep):
#         # if "Impl.i" not in query:
#         #     continue
#         orgi_path = orgi.clean_dir + "/" + query
#         if not os.path.exists(orgi_path):
#             orgi_path = orgi_path.replace("dfy.", "dfyxxx")
#         if not os.path.exists(orgi_path):
#             orgi_path = orgi_path.replace(".smt2", ".1.smt2")
#         asserts = get_dfy_asserts(orgi_path)

#         row = []
#         for k in ASSERT_LABELS:
#             row.append(asserts[k])
#         assert (asserts["goal"] == 1)
#         pts0.append(row)

#         mini_path = mini.clean_dir + "/" + query
#         asserts = get_dfy_asserts(mini_path)
#         row = []
#         for k in ASSERT_LABELS:
#             row.append(asserts[k])
#         assert (asserts["goal"] == 1)
#         pts1.append(row)

#     # print(pts0)
#     # print(pts1)
    
#     pts0 = np.array(pts0, dtype=np.float64)
#     pts1 = np.array(pts1, dtype=np.float64)

#     # for i in range(pts0.shape[0]):
#     #     pts0[i, :] = pts0[i, :] * 100 / np.sum(pts0[i, :])
#     #     pts1[i, :] = pts1[i, :] * 100 / np.sum(pts1[i, :])

#     table = [ASSERT_LABELS]
#     table.append(np.round(np.mean(pts0, axis=0), 2))
#     table.append(np.round(np.mean(pts1, axis=0), 2))
#     table.append(np.round(np.divide(np.mean(pts0, axis=0), np.mean(pts1, axis=0)), 2))
#     print(tabulate(table, headers="firstrow", tablefmt="github"))

# orgi = c.load_known_project("fs_vwasm")
# for i, q in enumerate(orgi.list_queries()):
#     # get file size
#     fs0 = get_assert_size(q)
#     print(fs0, q)

# plot_quanti()

# def get_fstar_assert_label():
#     # f = open("woot.smt2", "r")
#     o, _, _ = subprocess_run('grep -E "qid [^\)]+" -o woot.smt2')
#     qids = o.split("\n")
#     prelude = 0
#     typing = 0
#     lowstar = 0
#     others = 0
#     for qid in sorted(qids):
#         if "FStar" in qid:
#             prelude += 1
#         elif "Prims" in qid:
#             prelude += 1
#         # elif "qid typing" in qid or "kinding" in qid:
#         #     typing += 1
#         # elif "LowStar" in qid:
#         #     lowstar += 1
#         # else:
#         #     others +=1 
#             print(qid)
#     print(prelude, typing, lowstar, others)

# get_fstar_assert_label()



