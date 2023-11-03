from basic_utils import *
from db_utils import *
from cache_utils import *

from plot_utils import *
from configer import Configer
from unsat_core_build import *

# def print_compare_table(items0, ps0, items1, ps1):
#     table = [["category", "original", "minimized"]]
#     for cat in items0:
#         r0 = round(ps0[cat], 2)
#         r1 = round(ps1[cat], 2)
#         if r0 == 0 and r1 == 0:
#             continue
#         table.append([cat, f"{len(items0[cat])} ({r0})", f"{len(items1[cat])} ({r1})"])
#     print(tabulate(table, headers="firstrow", tablefmt="github"))

# def plot_instability_reduction():
#     fig, ax = plt.subplots()
#     x = 0

#     # pts = np.zeros((len(PAIRS), 4))
#     # for i, origi in enumerate(PAIRS):
#     #     mini = PAIRS[origi]
#     #     items0, items1, keep = get_basic_keep(origi, mini)
#     #     ps0, _ = get_category_percentages(items0)
#     #     ps1, _ = get_category_percentages(items1)
#     #     pts[i] = ps0[Stability.UNSTABLE], len(items0[Stability.UNSTABLE]), ps1[Stability.UNSTABLE], len(items1[Stability.UNSTABLE])
#     # print(pts.tolist())

#     pts = [[5.583756345177665, 110.0, 1.6751269035532994, 33.0], [3.187721369539551, 162.0, 1.338055883510429, 68.0], [3.920031360250882, 200.0, 1.1760094080752646, 60.0], [1.0980966325036603, 15.0, 0.36603221083455345, 5.0], [0.06134969325153374, 1.0, 0.18404907975460122, 3.0]]

#     ticks = []

#     for i, k in enumerate(PAIRS.keys()):
#         plt.bar(x, height=pts[i][0], label="original")
#         plt.text(x, pts[i][0], f"{int(pts[i][1])}")
#         ticks.append(x + 0.5)
#         plt.bar(x+1, height=pts[i][2], label="reduced")
#         plt.text(x+1, pts[i][2], f"{int(pts[i][3])}")
#         x += 4

#     plt.title("Unsat Core Instability Difference")
#     plt.xticks(ticks, PAIRS.keys())
#     plt.ylabel("percentage of unstable queries")
#     plt.savefig("fig/context/instability_diff.png", dpi=200)
#     plt.close()

# def get_quanti_stats(query_path):
#     fcount = 0
#     ecount = 0
#     qf = 0
#     nqf = 0
#     others = 0

#     for line in open(query_path).readlines():
#         quanti = False
#         if not line.startswith("(assert"):
#             others += 1
#             continue
#         cfc = line.count("(forall")
#         if cfc > 0:
#             quanti = True
#             fcount += cfc

#         cec = line.count("(exists")

#         if cec > 0:
#             quanti = True
#             ecount += cec

#         if not quanti:
#             qf += 1
#         else:
#             nqf += 1
#     return fcount, ecount, qf, nqf, others

# def load_quanti_keep_stats(orgi_name):
#     if os.path.exists(f"cache/{orgi_name}_keep_quanti.pkl"):
#         pts = cache_load(f"{orgi_name}_keep_quanti.pkl")
#     else:
#         mini_name = PAIRS[orgi_name]
#         items0, items1, keep = get_basic_keep(orgi_name, mini_name)
#         pts = np.zeros((len(keep), 10))
#         for i, q in enumerate(tqdm(keep)):
#             pts[i] = get_quanti_stats(keep[q][0]) \
#                 + get_quanti_stats(keep[q][1])
#         cache_save(pts, f"{orgi_name}_keep_quanti.pkl")
#     return pts

# def get_assert_size(query_path):
#     size = 0
#     for line in open(query_path).readlines():
#         if line.startswith("(assert"):
#             size += len(line)
#     return size

# def plot_context_reduction():
#     fig, ax = plt.subplots()

#     for orgi_name in PAIRS.keys():
#         pts = load_quanti_keep_stats(orgi_name)
#         # print((pts[:, 2] + pts[:, 3]) * 100 / (pts[:, 7] + pts[:, 8]))
#         xs, ys = get_cdf_pts((pts[:, 7] + pts[:, 8]) * 100 / (pts[:, 2] + pts[:, 3]) )
#         plt.plot(xs, ys, marker=",", label=orgi_name, linewidth=2)

#     plt.ylabel("cumulative percentage of queries")
#     plt.xlabel("percentage of assertions retained in unsat core (log scale)")
#     plt.title("Unsat Core Context Retention")
#     plt.legend()
#     plt.xscale("log")
#     plt.xlim(0.001, 100)
#     plt.ylim(0)
#     plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
#     plt.savefig("fig/context/context_retention.png", dpi=200)
#     plt.close()

#     fig, ax = plt.subplots()

#     for k in PAIRS.keys():
#         if os.path.exists(f"cache/{k}_assert_size.pkl"):
#             pts = cache_load(f"{k}_assert_size.pkl")
#         else:
#             items0, items1, keep = get_basic_keep(k, PAIRS[k])
#             pts = np.zeros((len(keep),), dtype=np.float64)
#             for i, q in enumerate(tqdm(keep)):
#                 orgi_path, mini_path = keep[q]
#                 fs0 = get_assert_size(orgi_path)
#                 fs1 = get_assert_size(mini_path)
#                 pts[i] = fs1 / fs0
#             cache_save(pts, f"{k}_assert_size.pkl")
#         xs, ys = get_cdf_pts(pts * 100)
#         plt.plot(xs, ys, marker=",", label=k, linewidth=2)

#     plt.ylabel("cumulative percentage of queries")
#     plt.xlabel("percentage of assert bytes retained in unsat core (log scale)")
#     plt.legend()
#     plt.title("Unsat Core Size Retention")
#     plt.ylim(0)
#     plt.xscale("log")
#     plt.xlim(0.001, 100)
#     plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
#     # ax.xaxis.set_major_formatter(mtick.PercentFormatter(xmax=1.0, decimals=3))
#     plt.savefig("fig/context/size_retention.png", dpi=200)
#     plt.close()

    # fig, ax = plt.subplots(3, 1)
    # fig.set_size_inches(7, 12)

    # for p in UNSAT_CORE_PROJECTS.values():
    #     data = p.get_patched_diff_stats()
    #     indices = np.where(data[:,3] == 0)
    #     xs, ys = get_cdf_pts(data[indices][:,4]/data[indices][:,0] * 100)
    #     ax[0].plot(xs, ys, marker=",", linewidth=2, label=p.name)

    #     xs, ys = get_cdf_pts(data[indices][:,4])
    #     ax[1].plot(xs, ys, marker=",", linewidth=2)
        
    #     indices = np.where(data[:,3] != 0)

    #     xs, ys = get_cdf_pts(data[indices][:,3]/data[indices][:,1] * 100)
    #     ax[2].plot(xs, ys, marker=",", linewidth=2)

    # ax[0].set_ylim(0, 100)
    # ax[0].set_xlim(0, 100)
    # ax[0].set_ylabel("cumulative percentage of queries")
    # ax[0].set_xlabel("percentage of asserts dropped")
    # ax[0].legend()

    # ax[1].set_ylim(0, 100)
    # ax[1].set_xlim(0, 200)
    # ax[1].set_ylabel("cumulative percentage of queries")
    # ax[1].set_xlabel("number of asserts dropped")

    # ax[2].set_ylim(0, 100)
    # ax[2].set_xlim(0, 100)
    # ax[2].set_ylabel("cumulative percentage of queries")
    # ax[2].set_xlabel("percentage of asserts added")

    # plt.suptitle("Updated Unsat Core Change (w.r.t Plain Unsat Core)")
    # plt.savefig("fig/context/updated_core_diff.png", dpi=200)
    # plt.close()
    
def filter_valid_dps(dps):
    nz = dps > 0
    nf = dps != np.inf
    return dps[np.logical_and(nz, nf)]

def plot_shake_max_depth(proj):
    s_dps = []
    u_dps = []
    dps = []

    for qm in proj.qms:
        if qm.orig_status == Stability.UNSTABLE:
            u_dps.append(qm.get_shake_stats())
        elif qm.orig_status == Stability.STABLE:
            s_dps.append(qm.get_shake_stats())

    s_dps = np.array(s_dps)
    u_dps = np.array(u_dps)
    dps = np.array(dps)

    xs, ys = get_cdf_pts(u_dps[:, 1])
    x_max = np.max(xs)
    plt.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="unstable original", color="red", drawstyle='steps-post')

    xs, ys = get_cdf_pts(filter_valid_dps(u_dps[:, 4]))
    x_max = max(np.max(xs), x_max)
    print(xs)
    plt.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="unstable core", linestyle="--", color="red", drawstyle='steps-post')

    xs, ys = get_cdf_pts(s_dps[:, 1])
    x_max = max(np.max(xs), x_max)
    plt.plot(xs, ys, marker=",", linewidth=2, label="stable original", color="blue", drawstyle='steps-post')

    nz = s_dps[:, 5] > 0
    nf = s_dps[:, 5] != np.inf
    misses = np.sum(np.logical_and(nz, nf))
    print(proj.name, "shake missed ", misses, "/", len(nf))

    xs, ys = get_cdf_pts(filter_valid_dps(s_dps[:, 4]))
    x_max = max(np.max(xs), x_max)
    plt.plot(xs, ys, marker=",", linewidth=2, label="stable core", linestyle="--", color="blue", drawstyle='steps-post')

    plt.ylabel("cumulative percentage of queries")
    plt.xlabel("maximum assertion depth")
    plt.ylim(0, 100)
    plt.xlim(left=0, right=x_max)
    plt.xticks(np.arange(0, x_max+1, 1))
    plt.grid(True)
    plt.title(f"Shake Assertion Max Depth Distribution {proj.name}")

    plt.legend()
    plt.savefig(f"fig/context/shake_{proj.name}.png", dpi=200)
    plt.close()

# def plot_shake_mean_depth(proj):
#     s_dps = []
#     u_dps = []
#     dps = []

#     for qm in proj.qms:
#         if qm.orig_status == Stability.UNSTABLE:
#             u_dps.append(qm.get_shake_stats())
#         elif qm.orig_status == Stability.STABLE:
#             s_dps.append(qm.get_shake_stats())

#     s_dps = np.array(s_dps)
#     u_dps = np.array(u_dps)
#     dps = np.array(dps)

#     xs, ys = get_cdf_pts(u_dps[:, 0])
#     x_max = np.max(xs)
#     plt.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="unstable original", color="red", drawstyle='steps-post')

#     xs, ys = get_cdf_pts(filter_valid_dps(u_dps[:, 3]))
#     x_max = max(np.max(xs), x_max)
#     plt.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="unstable core", linestyle="--", color="red", drawstyle='steps-post')

#     xs, ys = get_cdf_pts(s_dps[:, 0])
#     x_max = max(np.max(xs), x_max)
#     plt.plot(xs, ys, marker=",", linewidth=2, label="stable original", color="blue", drawstyle='steps-post')

#     xs, ys = get_cdf_pts(filter_valid_dps(s_dps[:, 3]))
#     x_max = max(np.max(xs), x_max)
#     plt.plot(xs, ys, marker=",", linewidth=2, label="stable core", linestyle="--", color="blue", drawstyle='steps-post')

#     plt.ylabel("cumulative percentage of queries")
#     plt.xlabel("mean assertion depth")
#     plt.ylim(0, 100)
#     plt.xlim(left=0, right=x_max)
#     plt.xticks(np.arange(0, x_max+1, 1))
#     plt.grid(True)
#     plt.title(f"Shake Assertion Mean Depth Distribution {proj.name}")

#     plt.legend()
#     plt.savefig(f"fig/context/shake_mean_{proj.name}.png", dpi=200)
#     plt.close()

if __name__ == "__main__":
    for proj in UNSAT_CORE_PROJECTS.values():
        plot_shake_max_depth(proj)
        # plot_shake_mean_depth(proj)