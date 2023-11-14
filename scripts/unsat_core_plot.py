from basic_utils import *
from db_utils import *
from cache_utils import *

from plot_utils import *
from configer import Configer
from unsat_core_build import *
import plotly.graph_objects as go
import plotly
import re

# def plot_instability_change():
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


# def get_assert_size(query_path):
#     size = 0
#     for line in open(query_path).readlines():
#         if line.startswith("(assert"):
#             size += len(line)
#     return size

def plot_all_context_retention():
    fig, ax = plt.subplots()

    for proj in UNSAT_CORE_PROJECTS.values():
        pts = proj.get_assert_counts(True)
        xs, ys = get_cdf_pts(pts[:, 1] * 100 / pts[:, 0])
        plt.plot(xs, ys, marker=",", label=proj.name, linewidth=2)

    plt.ylabel("cumulative percentage of queries")
    plt.xlabel("percentage of assertions retained in unsat core (log scale)")
    plt.title("Unsat Core Context Retention")
    plt.legend()
    plt.xscale("log")
    plt.xlim(0.001, 100)
    plt.ylim(0, 100)
    plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    plt.savefig("fig/context/retention_core.png", dpi=200)
    plt.close()

def plot_all_shake_context_retention():
    figure, axis = setup_fig(len(UNSAT_CORE_PROJECTS), 2)

    for i, proj in enumerate(UNSAT_CORE_PROJECTS.values()):
        plot_shake_context_retention(axis[i], proj)

    plt.savefig(f"fig/context/retention_shake.png", dpi=200)
    plt.close()

def plot_shake_context_retention(sps, proj):
    if cache_exists(f"shake_retention_{proj.name}"):
        pts = cache_load(f"shake_retention_{proj.name}")
    else:
        pts = np.zeros((len(proj.qms), 4))
        for i, qm in enumerate(tqdm(proj.qms)):
            o_asserts = get_assert_count(qm.orig_path)
            m_asserts = get_assert_count(qm.mini_path)
            stats = qm.get_shake_stats()
            s_o_asserts = qm.get_shake_assert_count(stats[4])
            s_p_asserts = qm.get_shake_assert_count()
            pts[i] = o_asserts, m_asserts, s_o_asserts, s_p_asserts
        cache_save(pts, f"shake_retention_{proj.name}")

    xs, ys = get_cdf_pts(pts[:, 1] * 100 / pts[:, 0])
    sps[0].plot(xs, ys, marker=",", label="unsat-core", linewidth=2)
    sps[1].plot(xs, ys, marker=",", label="unsat-core", linewidth=2)

    xs, ys = get_cdf_pts(pts[:, 2] * 100 / pts[:, 0])
    sps[0].plot(xs, ys, marker=",", label="shake-oracle", linewidth=2)
    sps[1].plot(xs, ys, marker=",", label="shake-oracle", linewidth=2)

    xs, ys = get_cdf_pts(pts[:, 3] * 100 / pts[:, 0])
    sps[0].plot(xs, ys, marker=",", label="shake-plain", linewidth=2)
    sps[1].plot(xs, ys, marker=",", label="shake-plain", linewidth=2)

    sps[0].set_ylabel("cumulative percentage of queries")
    sps[0].set_xlabel("percentage of assertions retained in unsat core (log scale)")
    sps[1].set_xlabel("percentage of assertions retained in unsat core")
    
    sps[0].set_title(f"Unsat Core Context Retention {proj.name}")

    sps[0].legend()
    sps[1].legend()

    sps[0].set_xscale("log")
    sps[0].set_xlim(0.001, 100)
    sps[0].set_xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])

    sps[1].set_xlim(0, 100)

    sps[0].set_ylim(0, 100)
    sps[1].set_ylim(0, 100)

def filter_valid_dps(dps):
    return dps[dps != np.inf]

def plot_shake_max_depth(sp, proj):
    s_dps = []
    u_dps = []
    dps = []

    for qm in proj.qms:
        stats = qm.get_shake_stats()
        if qm.orig_status == Stability.UNSTABLE:
            u_dps.append(stats)
        elif qm.orig_status == Stability.STABLE:
            s_dps.append(stats)
        dps.append(stats)

    s_dps = np.array(s_dps)
    u_dps = np.array(u_dps)
    dps = np.array(dps)

    # xs, ys = get_cdf_pts(dps[:, 1])
    # x_max = np.max(xs)
    # sp.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="original", drawstyle='steps-post')
    
    # xs, ys = get_cdf_pts(filter_valid_dps(dps[:, 4]))
    # x_max = max(np.max(xs), x_max)
    # sp.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="core", linestyle="--", drawstyle='steps-post')

    xs, ys = get_cdf_pts(u_dps[:, 1])
    x_max = np.max(xs)
    sp.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="unstable original", color="red", drawstyle='steps-post')

    xs, ys = get_cdf_pts(filter_valid_dps(u_dps[:, 4]))
    x_max = max(np.max(xs), x_max)
    sp.plot(np.insert(xs, 0, 0), np.insert(ys, 0, 0), marker=",", linewidth=2, label="unstable core", linestyle="--", color="red", drawstyle='steps-post')

    xs, ys = get_cdf_pts(s_dps[:, 1])
    x_max = max(np.max(xs), x_max)
    sp.plot(xs, ys, marker=",", linewidth=2, label="stable original", color="blue", drawstyle='steps-post')

    xs, ys = get_cdf_pts(filter_valid_dps(s_dps[:, 4]))
    x_max = max(np.max(xs), x_max)
    sp.plot(xs, ys, marker=",", linewidth=2, label="stable core", linestyle="--", color="blue", drawstyle='steps-post')

    sp.set_ylabel("cumulative percentage of queries")
    sp.set_xlabel("maximum assertion depth")
    sp.set_ylim(0, 100)
    sp.set_xlim(left=0, right=x_max)
    sp.set_xticks(np.arange(0, x_max+1, 1))
    sp.grid(True)
    sp.legend()
    sp.set_title(f"Shake Assertion Max Depth Distribution {proj.name}")

def plot_all_shake_max_depth():
    figure, axis = setup_fig(len(UNSAT_CORE_PROJECTS), 1)

    for i, proj in enumerate(UNSAT_CORE_PROJECTS.values()):
        plot_shake_max_depth(axis[i], proj)

    plt.savefig(f"fig/context/shake_max_depth.png", dpi=200)
    plt.close()

def plot_shake_incomplete(proj):
    dps = []

    for qm in proj.qms:
        stats = qm.get_shake_stats(unify=True)
        dps.append(stats)

    dps = np.array(dps)

    nz = dps[:, 5] > 0
    nf = np.isfinite(dps[:, 5])

    misses = np.sum(np.logical_and(nz, nf))
    print(proj.name, "shake missed ", misses, "/", np.sum(nf), "/", len(proj.qms))

def plot_migration(proj):
    mini_cats = proj.mini_cats
    orig_cats = proj.orig_cats
    extd_cats = proj.extd_cats

    unified = deepcopy(mini_cats)
    changed = set()
    for i in unified[Stability.UNSOLVABLE]:
        new_cat = find_category(i, extd_cats)
        if new_cat != None:
            changed.add(i)
            unified[new_cat].add(i)

    # TODO: maybe consider the missing cores, which may have been solved by the extension

    unified[Stability.UNSOLVABLE] -= changed
    extd_cats = unified

    o_labels = {"o_" + k: k for k, v in orig_cats.items() if len(v) > 0}
    m_labels = {"m_" + k: k for k, v in mini_cats.items() if len(v) > 0}
    e_labels = {"e_" + k: k for k, v in extd_cats.items() if len(v) > 0}

    colors = []
    srcs = []
    dsts = []
    values = []

    all_labels = ['o_stable', 'o_unstable', 'o_unsolvable', 
    'm_stable', 'm_unstable', 'm_unsolvable',  'm_no_core', 
    'e_stable', 'e_unstable', 'e_unsolvable']

    assert set.union(*[key_set(o_labels), key_set(m_labels), key_set(e_labels)]) == set(all_labels) - {"m_no_core"}

    for l in all_labels:
        if "_stable" in l:
            colors.append("green")
        elif "_unstable" in l:
            colors.append("red")
        elif "_unsolvable" in l:
            colors.append("blue")
        else:
            colors.append("black")

    o_tally = set.union(*orig_cats.values())
    m_tally = set.union(*mini_cats.values())
    e_tally = set.union(*extd_cats.values())

    for ol in o_labels:
        for ml in m_labels:
            srcs.append(all_labels.index(ol))
            dsts.append(all_labels.index(ml))
            values.append(len(orig_cats[o_labels[ol]] & mini_cats[m_labels[ml]]))

    uncovered = o_tally - m_tally

    for ol in o_labels:
        srcs.append(all_labels.index(ol))
        dsts.append(all_labels.index("m_no_core"))
        values.append(len(orig_cats[o_labels[ol]] & uncovered))

    for ml in m_labels:
        for el in e_labels:
            srcs.append(all_labels.index(ml))
            dsts.append(all_labels.index(el))
            values.append(len(mini_cats[m_labels[ml]] & extd_cats[e_labels[el]]))

    fig = go.Figure(data=[go.Sankey(
                            # arrangement = "freeform",
                            node = dict(
                                label =  all_labels,
                                # color =  colors
                                pad = 10,
                            ),
                            link = dict(
                            source =  srcs,
                            target =  dsts,
                            value =  values,
                            )
                        )
                    ])

    fig.update_layout(title_text=f"{proj.name} stability migration", font_size=10)
    # fig.write_image(f"fig/context/migration/{proj.name}.png", width=800, height=600, scale=2)
    plotly.offline.plot(fig, filename=f"fig/context/migration/{proj.name}.html")

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

def analyze_fs_dice():
    proj = UNSAT_CORE_PROJECTS["fs_dice"]
    for qm in proj.qms:
        if qm.base == "queries-L0.Impl.Certificate-14.smt2":
            break

    print(qm.orig_status)
    print(qm.extd_status)
    print(qm.extd_status)
    # print(qm.get_shake_stats(True))
    # qm.shake_from_log(4)
    stamps = parse_stamps(qm.shke_log_path)

    temp = "temp/shake.smt2"
    qid_pattern = re.compile("qid [^\)]+")
    orig_asserts = get_asserts(qm.orig_path)
    mini_asserts = get_asserts(qm.mini_path)
    temp_asserts = get_asserts(temp)
    
    # os.system(f"cp {qm.orig_path} temp/woot.smt2")
    # os.system(f"cp {qm.mini_path} temp/core.smt2")
    # os.system(f"cp {qm.extd_path} temp/extd.smt2")

    # for a in temp_asserts:
    #     finds = re.findall(qid_pattern, mini_asserts[a])
    #     for i in finds:
    #         print(i)
    #     if len(finds) != 0:
    #         print("")

    for a, c in temp_asserts.items() - mini_asserts.items():
        finds = re.findall(qid_pattern, c)
        if len(finds) != 0:
            print(c)
            if a in stamps:
                print(stamps[a])
            else:
                print("inf")
            for i in finds:
                print(i)

            print("")
    # print(len(orig_asserts), len(mini_asserts), len(temp_asserts))

if __name__ == "__main__":
    analyze_fs_dice()
    # for proj in UNSAT_CORE_PROJECTS.values():
    #     # plot_shake_incomplete(proj)
    #     plot_migration(proj)

    # plot_all_shake_max_depth()
    # plot_all_context_retention()
    # plot_all_shake_context_retention()
