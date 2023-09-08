from basic_utils import *
from db_utils import *
from vbkv_filemap import *

from plot_utils import *
from configer import Configer
from analyze_unsat_core import *
from cache_utils import cache_load, cache_save
from categorize_qids import *

import random

c = Configer()

def sample_then_remove_all_triggers(orgi_name, pruned_name):
    orgi = c.load_known_project(orgi_name)
    pruned = c.load_known_project(pruned_name)
    prefix = pruned.clean_dir

    for q in orgi.list_queries(1, 10):
        base = q.split("/")[-1]
        print(f"./target/release/mariposa --in-file-path {q} --out-file-path {prefix}/{base} -m remove-trigger")

    # for q in list_smt2_files(prefix):
    #     print(f"./target/release/mariposa --in-file-path {q}")

def format_item(count, total):
    return f"{int(count)} ({round(count * 100 / total, 0)}%)"

def print_assertion_distribution():
    tpts = []

    for orgi_name in PAIRS.keys():
        pts = load_quanti_stats(orgi_name)
        total = pts[:, 2] + pts[:, 3] + pts[:, 4]
        pts = pts[(pts[:, 2]/total).argsort()]
        total = pts[:, 2] + pts[:, 3] + pts[:, 4]
        qf, nqf, others = pts[:, 2], pts[:, 3], pts[:, 4]

        row = [orgi_name]
        tt = np.median(total)
        row.append(int(tt))
        row.append(format_item(np.median(others), tt))
        row.append(format_item(np.median(qf), tt))
        row.append(format_item(np.median(nqf), tt))

        qf, nqf, others = qf * 100 /total, nqf * 100 /total, others * 100 /total
    
        xs = np.arange(0, len(pts[:, 1]), 1)
        fig, ax = plt.subplots()
        plt.fill_between(xs, nqf, label="Q-assert")
        plt.fill_between(xs, nqf, nqf + qf, label="QF-assert")
        plt.fill_between(xs, nqf + qf, nqf + qf + others, label="N-assert")
        plt.ylim(0)
        plt.xlim(0, len(xs))
        plt.legend()
        plt.savefig(f"fig/quanti/{orgi_name}_commands.png", dpi=200)
        plt.close()
        tpts.append(row)

    print(tabulate(tpts, ["project", "total", "n-assert", "qf-assert", "q-assert"], tablefmt="latex"))

def print_quantifier_distribution():
    tpts = []
    # fig, ax = plt.subplots()

    for orgi_name in PAIRS.keys():
        pts = load_quanti_stats(orgi_name)
        forall, exists, nqf = pts[:, 0], pts[:, 1], pts[:, 3]
        row = [orgi_name]
        row.append(np.median(forall))
        row.append(np.mean(forall/nqf))
        row.append(np.median(exists))
        row.append(np.mean(exists/nqf))
        tpts.append(row)

    print(tabulate(tpts, ["project", 
                          "forall per-qeury", "per-quantified-assert", 
                          "exists per-query", "per-quantified-assert"]))

    # plt.plot(xs, ys, marker=",", label="forall", linewidth=2)
    # plt.legend()
    # plt.savefig(f"fig/quanti/quanti.png", dpi=200)

def load_prelude_stats(pname):
    project = c.load_known_project(pname)
    if os.path.exists(f"cache/{pname}_preldue.pkl"):
        pts = cache_load(f"{pname}_preldue.pkl")
    else:
        pts = np.zeros((len(project.list_queries()), 2))
        for i, q in enumerate(tqdm(project.list_queries())):
            if project.framework == "fstar":
                pts[i] = get_fs_assert_label(q)
            else:
                assert project.framework == "dafny"
                pts[i] = get_dfy_assert_label(q)
        cache_save(pts, f"{pname}_preldue.pkl")
    return pts

def plot_prelude():
    fig, ax = plt.subplots()
    for orgi_name in PAIRS.keys():
        pts = load_prelude_stats(orgi_name)
        xs, ys = get_cdf_pts(pts[:, 0] * 100 / (pts[:, 1] + pts[:, 0]))
        plt.plot(xs, ys, marker=",", label=f"{orgi_name}", linewidth=2)

    plt.xscale("log")
    plt.xlim(1, 100)
    plt.ylim(0)
    plt.xticks([1.0, 10, 100], ["1%", "10%", "100%"])

    plt.xlabel("percentage of quantifiers from prelude (log scale)")
    plt.ylabel("cumulative percentage of queries")

    plt.legend()
    plt.savefig(f"fig/quanti/prelude.png", dpi=200)

if __name__ == "__main__":
    # sample_then_remove_all_triggers("d_komodo", "d_komodo_10_percent_sample_no_trigger")
    # sample_then_remove_all_triggers("fs_vwasm", "fs_vwasm_10_percent_sample_no_trigger")
    sample_then_remove_all_triggers("fs_dice", "fs_dice_10_percent_sample_no_trigger")

    # print_assertion_distribution()
    # print_quantifier_distribution()
    # plot_prelude()
    # print(get_quanti_stats(sys.argv[1]))
