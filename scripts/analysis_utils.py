from db_utils import *
from vbkv_filemap import *
import shutil

from plot_utils import *
import matplotlib.pyplot as plt
import multiprocessing as mp
from configer import Configer

c = Configer()

MAIN_EXP = c.load_known_experiment("main")

S_KOMODO = c.load_known_project("s_komodo")
D_KOMODO = c.load_known_project("d_komodo")
D_FVBKV = c.load_known_project("d_fvbkv")
D_LVBKV = c.load_known_project("d_lvbkv")
FS_VWASM = c.load_known_project("fs_vwasm")
FS_DICE = c.load_known_project("fs_dice")


MAIN_PROJS = [S_KOMODO, D_KOMODO, D_FVBKV, D_LVBKV, FS_VWASM, FS_DICE]

Z3_4_4_2 = c.load_known_solver("z3_4_4_2")
Z3_4_5_0 = c.load_known_solver("z3_4_5_0")
Z3_4_6_0 = c.load_known_solver("z3_4_6_0")
Z3_4_8_5 = c.load_known_solver("z3_4_8_5")
Z3_4_8_8 = c.load_known_solver("z3_4_8_8")
Z3_4_8_11 = c.load_known_solver("z3_4_8_11")
Z3_4_11_2 = c.load_known_solver("z3_4_11_2")
Z3_4_12_1 = c.load_known_solver("z3_4_12_1")

MAIN_Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8, Z3_4_8_11, Z3_4_11_2, Z3_4_12_1]

MAIN_ANALYZER = c.load_known_analyzer("default")
Z_TEST_60 = Analyzer(.05, 60, .05, .95, 0.8, "z_test")
STRICT_60 = Analyzer(.05, 60, .05, .95, 0.8, "strict")

plt.rcParams['text.usetex'] = True
plt.rcParams["font.family"] = "serif"

FSIZE = 16
FNAME ='Times New Roman'

COLORS = [
    "#803E75", # Strong Purple
    "#FF6800", # Vivid Orange
    "#A6BDD7", # Very Light Blue
    "#C10020", # Vivid Red
    "#FFB300", # Vivid Yellow
    "#817066", # Medium Gray
    "#F6768E", # Strong Purplish Pink
]

PROJECT_LABELS = {
    "d_komodo": r"Komodo$_{D}$",
    "s_komodo": r"Komodo$_S$",
    "d_fvbkv": r"VeriBetrKV$_{D}$",
    "d_lvbkv": r"VeriBetrKV$_{L}$",
    "fs_dice": r"DICE$^\star_F$",
    "fs_vwasm": r"vWasm$_F$",
} 

SOLVER_LABELS = {
    "z3_4_4_2": r"Z3 4.4.2",
    "z3_4_5_0": r"Z3 4.5.0",
    "z3_4_6_0": r"Z3 4.6.0",
    "z3_4_8_5": r"Z3 4.8.5",
    "z3_4_8_8": r"Z3 4.8.8",
    "z3_4_8_11": r"Z3 4.8.11",
    "z3_4_11_2": r"Z3 4.11.2",
    "z3_4_12_1": r"Z3 4.12.1",
}

def make_title(proj, solver):
    # star = ""
    # if proj.artifact_solver == solver:
    #     star = r"$\star$"
    if solver.name in SOLVER_LABELS:
        return f"{PROJECT_LABELS[proj.name]} {SOLVER_LABELS[solver.name]}"
    return f"{PROJECT_LABELS[proj.name]} {solver.name}"

def get_color_map(keys):
    assert len(keys) <= len(COLORS)
    return {k: COLORS[i] for i, k in enumerate(keys)}

PROJECT_COLORS = get_color_map([c for c in PROJECT_LABELS])

MUTATION_COLORS = {
    "shuffle": "#803E75",        
    "rename": "#FF6800",
    "reseed": "#A6BDD7",
    "union": "#FFB300",
    "unstable": "#FFB300",
    "unsolvable": "#C10020",
    "intersect": "#817066",
}

MUTATION_LABELS = {
    "shuffle":r"shuffling",
    "reseed": r"reseeding",
    "rename": r"renaming",
}

def get_unknowns(proj, exp=MAIN_EXP):
    th = STRICT_60
    summary = load_sum_table(proj, proj.artifact_solver, exp)
    assert summary is not None
    categories = th.categorize_queries(summary)
    return categories[Stability.UNKNOWN]

def load_exp_sums(proj, skip_unknowns=True, solvers=None):
    summaries = dict()

    if skip_unknowns:
        unknowns = get_unknowns(proj)
    else:
        unknowns = set()

    if solvers == None:
        solvers = MAIN_Z3_SOLVERS

    for solver in solvers:
        nrows = load_sum_table(proj, solver, MAIN_EXP, skip=unknowns)
        if nrows is None:
            continue
        summaries[solver] = nrows
    return summaries

def _async_categorize_project(ratios, key, rows):
    ana = Z_TEST_60
    items = ana.categorize_queries(rows)
    ps, _ = get_category_percentages(items)
    ratios[key] = ps

def _mp_categorize_projects(projs, solvers):
    manager = mp.Manager()
    ratios = manager.dict()

    for proj in projs:
        summaries = load_exp_sums(proj)
        pool = mp.Pool(processes=8)
        for solver in solvers:
            key = (projs.index(proj), solvers.index(solver))
            rows = summaries[solver]
            pool.apply_async(_async_categorize_project, 
                            args=(ratios, key, rows,))
        pool.close()
        pool.join()

    category_count = len(Stability)
    data = np.zeros((len(projs), len(solvers), category_count))

    for key in ratios:
        i, j = key
        data[i][j] = [ratios[key][s] for s in Stability]

    return data

def plot_paper_overall():
    projs = MAIN_PROJS
    solvers = MAIN_Z3_SOLVERS
    
    project_names = [proj.name for proj in projs]
    solver_names = [SOLVER_LABELS[s] for s in MAIN_Z3_SOLVERS]
    solver_labels = [f"{SOLVER_LABELS[s]}\n{s.date[:-3]}" for s in MAIN_Z3_SOLVERS]

    data = _mp_categorize_projects(projs, solvers)
    
    # splits = [[0, 1], [2, 3], [4, 5]]
    
    # print(r"\toprule")
    
    # for split in splits:
    #     for j in range(len(solver_names)):
    #         if j == 0:
    #             plabels = [PROJECT_LABELS[project_names[i]] for i in split]
    #             plabels = [r"\multicolumn{4}{c|}{" +  p + "}" for p in plabels]
    #             plabels = [""] + plabels
    #             print(" & ".join(plabels), end=" ")
    #             print(r" \\ ")
    #             cats = [r"\unsolvable", r"\unstable", r"\inconclusive", r"\stable"]
    #             cats = [""] + cats * 2
    #             print(" & ".join(cats), end=r"\\")
    #             print("")
    #             # print("\unsolvable & \unstable & \inconclusive & \stable", end=" ")
    #         print(MAIN_Z3_SOLVERS[j].name, end=" & ")
    #         for i in split:
    #             project = data[i][j]
    #             entry = np.round(project[1:], 2).tolist()
    #             entry = r" & ".join(["%.2f" % e + r"\%"  for e in entry])
    #             if i == split[-1]:
    #                 print(entry, end=r" \\ ")
    #                 print("")
    #             else:
    #                 print(entry, end=" & ")    
    #     print("\hline")
    # print(r"\bottomrule")

    data = np.array(data)
    print(data.tolist())

    bar_width = len(solver_names)/70
    fig, ax = plt.subplots()
    fig.set_size_inches(15, 5)

    br = np.arange(len(solver_names))
    br = [x - 2 * bar_width for x in br]

    # data[project_index][solver_index][category_index]
    handles = []

    for pi, project_row in enumerate(data):
        pcs = np.zeros((len(Stability), len(solver_names)))

        br = [x + bar_width for x in br]
        for i, ps in enumerate(project_row):
            pcs[:, i] = ps
        pcolor = PROJECT_COLORS[project_names[pi]]
        pcs = np.cumsum(pcs,axis=0)

        plt.bar(br, height=pcs[1], width=bar_width,
                color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.2)
        hd = plt.bar(br, height=pcs[2]-pcs[1], bottom=pcs[1], width=bar_width,
                color=pcolor, edgecolor='black', linewidth=0.2)
        handles.append(hd)
        plt.bar(br, height=pcs[3]-pcs[2], bottom=pcs[2], width=bar_width,
                color="w", edgecolor='black', linewidth=0.2)

        for i in range(len(solver_names)):
            if solver_names[i] == str(projs[pi].artifact_solver):
                plt.scatter(br[i], pcs[3][i] + 0.2, marker="*", color='black',  linewidth=0.8, s=40)
            # if i == 4 and pi == 0:
            #     plt.bar(br[i], height=20, bottom=pcs[3][i], width=bar_width, 
            #             color='white', edgecolor='black', linewidth=0.3, linestyle=(0, (1, 5)))

    label_x = 2.85
    leable_y = 5
    ls = (0, (1, 5))
    
    plt.text(label_x, leable_y, r'\texttt{unsolvable}', horizontalalignment='right', fontsize=FSIZE)
    plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 1.0], 
             'o', ls=ls, color='black', linewidth=0.5, ms=1)
    leable_y += 0.8
    plt.text(label_x, leable_y, r'\texttt{unstable}', horizontalalignment='right', fontsize=FSIZE)
    plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 2.7],
             'o', ls=ls, color='black', linewidth=0.5, ms=1)
    leable_y += 0.8
    plt.text(label_x, leable_y, r'\texttt{inconclusive}', horizontalalignment='right', fontsize=FSIZE)
    plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 4.7],
             'o', ls=ls, color='black', linewidth=0.5, ms=1)
    # plt.text(3.5, 5.45, r'\texttt{stable}' + "\n" + r"stack up to 100\%" + "\n" + "(unplotted)", horizontalalignment='right')
    # plt.plot([3.55, 3.88], [6.40, 6.75], 'o', ls='-', color='black', linewidth=0.2, ms=2)

    ax.tick_params(axis='both', which='major')
    plt.xticks([r + 2 * bar_width for r in range(len(solver_names))], solver_labels, rotation=30, ha='right', fontsize=FSIZE)
    from matplotlib.lines import Line2D
    woot = Line2D([0], [0], marker="*", color='black', linestyle='None', label='artifact solver'),
    plt.legend(handles + [woot],  [PROJECT_LABELS[p] for p in project_names] + ['artifact solver'], loc='upper left', fontsize=FSIZE)
    plt.ylabel(r'query proportion ($\%$)', fontsize=FSIZE, fontname=FNAME)
    plt.xlabel('solver versions and release dates', fontsize=FSIZE, fontname=FNAME)
    plt.ylim(bottom=0, top=9)
    plt.tight_layout()
    plt.savefig("fig/all_paper.pdf")
    plt.close()

def _get_data_time_scatter(rows):
    pf, cfs = 0, 0
    ps, css = 0, 0

    ana = MAIN_ANALYZER
    cats = {i: [] for i in Stability }

    scatters = np.zeros((len(rows), 2))
    for i, query_row in enumerate(rows):
        group_blobs = query_row[2]

        plain_res = group_blobs[0][0][0]
        plain_time = group_blobs[0][1][0]
        mutants = np.hstack((group_blobs[0,:,1:], group_blobs[1,:,1:], group_blobs[2,:,1:]))

        cat = ana.categorize_query(group_blobs)[0]
        cats[cat].append(i)

        valid_indices = mutants[0] == RCode.UNSAT.value
        success = np.sum(valid_indices)
        ts = np.median(mutants[1])
    
        if plain_res != RCode.UNSAT.value:
            pf += 1
            if success == 0:
                cfs += 1
        else:
            ps += 1
            if success == 180:
                css += 1
        scatters[i][0] = plain_time/1000
        scatters[i][1] = ts/1000
    return cats, scatters

def _plot_time_scatter(rows, sp):
    cats, scatters = _get_data_time_scatter(rows)
    # others = list(set(range(len(rows))) - set(cats[Stability.STABLE]) - set(cats[Stability.UNSTABLE]))
    
    stables = cats[Stability.STABLE]
    unstables = cats[Stability.UNSTABLE]
    unsolvables = cats[Stability.UNSOLVABLE] + cats[Stability.UNKNOWN]
    inconclusives = cats[Stability.INCONCLUSIVE]

    sp.scatter(scatters[:,0][stables], scatters[:,1][stables], s=8, color="#78A1BB", label=r"\texttt{stable}")
    sp.scatter(scatters[:,0][unstables], scatters[:,1][unstables], s=8, color="orange", label=r"\texttt{unstable}")
    sp.scatter(scatters[:,0][unsolvables], scatters[:,1][unsolvables], s=8, color="r", marker="s", label=r"\texttt{unsolvable}")
    sp.scatter(scatters[:,0][inconclusives], scatters[:,1][inconclusives], s=8, label=r"\texttt{inconclusive}")
    
    # sp.scatter(scatters[:,0][[cats[Stability.Unk]], scatters[:,1][others], s=8, label="others")
    # print(pf, cfs, ps, css)
    # print(percentage(bounded, len(scatters)), mworse, len(scatters))
    # print(weightstats.ttost_paired(np.array(ys), np.array(xs), -0.57, -0.03))
    # print(weightstats.ttost_paired(np.array(ys), np.array(xs), 1.002, 1.015, transform=np.log))
    sp.fill_between([0.01, 1000],  [0.01 * 1.5, 1000 * 1.5], [0.01, 1000], alpha=0.1, color="green", label=r"$\frac{x}{1.5} < y < 1.5x$")
    sp.fill_between([0.01, 1000],  [0.01, 1000], [0.01 / 1.5, 1000 / 1.5], alpha=0.1, color="green")
    # sp.loglog([0.01, 1000], [0.01, 1000], color="black", linestyle="--",linewidth=0.75)
    sp.set_xlim(left=.1, right=160)
    sp.set_ylim(bottom=.1, top=160)
    sp.set_xscale("log")
    sp.set_yscale("log")
    handles, labels = sp.get_legend_handles_labels()
    order = [2,1,0,3, 4]
    sp.legend([handles[idx] for idx in order],[labels[idx] for idx in order])
    sp.set_aspect('equal', adjustable='box')

def plot_paper_time_scatter():
    figure, axis = plt.subplots(1, 2)
    figure.set_size_inches(7, 4)
    solver = Z3_4_12_1
    for i, proj in enumerate([D_KOMODO, FS_VWASM]):
        rows = load_exp_sums(proj, True, [solver])[solver]
        axis[i].set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        _plot_time_scatter(rows, axis[i])
    figure.supxlabel("original time (seconds)", fontsize=FSIZE, fontname=FNAME)
    figure.supylabel("median mutant time (seconds)", fontsize=FSIZE, fontname=FNAME)
    plt.tight_layout()
    plt.savefig(f"fig/time_scatter/scatter_paper.pdf")
    plt.close()

def plot_appendix_time_scatter():
    rc, cc = 2, 4
    for proj in tqdm(MAIN_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)

        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(MAIN_Z3_SOLVERS):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_time_scatter(rows, sp)
            sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("original time (seconds)", fontsize=FSIZE, fontname=FNAME)
        figure.supylabel("median mutant time (seconds)", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()
        plt.savefig(f"fig/time_scatter/{proj.name}.pdf")
        plt.close()

def _get_data_time_std(rows):
    ana = Z_TEST_60

    items = ana.categorize_queries(rows)
    stables = items['stable']

    dps = [[], [], []]
    for query_row in rows:
        query_path = query_row[0]
        if query_path not in stables:
            continue
        group_blobs = query_row[2]

        for k in range(group_blobs.shape[0]):
            ts = group_blobs[k][1] 
            bs = np.clip(ts, 0, 6e4) / 1000
            dps[k].append(np.std(bs))
    return dps

def _plot_time_std(exp, rows, sp):
    y_bound = 0
    x_bound = 0
    dps = _get_data_time_std(rows)
    mutations = [str(p) for p in exp.enabled_muts]

    for i in range(len(mutations)):
        xs, ys = get_cdf_pts(dps[i])
        ys = np.flip(ys)
        try:
            start = np.where(xs > 1)[0][0]
        except:
            start = -1
        y_bound = max(ys[start-1], y_bound)
        x_bound = max(np.max(xs), x_bound)
        label = MUTATION_LABELS[mutations[i]]
        color = MUTATION_COLORS[mutations[i]]
        sp.plot(xs, ys, label=label, color=color)
    sp.set_xlim(left=1)
    ticks = [1, 5, 10, 15, 20]
    sp.set_xticks(ticks)
    sp.set_ylim(bottom=0, top=y_bound)

def plot_appendix_time_std():
    rc, cc = 2, 4

    for proj in tqdm(MAIN_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(MAIN_Z3_SOLVERS):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_time_std(MAIN_EXP, rows, sp)
            sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
            sp.legend()
        figure.supylabel(r"proportion of queries exceding ($\%$)", fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("time standard deviation (seconds)", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()
        plt.savefig(f"fig/time_stable/{proj.name}.pdf")
        plt.close()    

def plot_paper_time_std():
    figure, axis = plt.subplots(1, 2, figsize=(7, 4))
    # figure.set_size_inches(7, 4.2)
    solver = Z3_4_12_1
    for index, proj in enumerate([D_KOMODO, FS_DICE]):
        sp = axis[index]
        rows = load_exp_sums(proj, True, [solver])[solver]
        _plot_time_std(MAIN_EXP, rows, sp)
        sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        sp.legend()

    figure.supylabel(r"proportion of queries exceding ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time standard deviation (seconds)", fontsize=FSIZE, fontname=FNAME)
    plt.tight_layout()
    plt.savefig(f"fig/time_stable/std_paper.pdf")
    plt.close()    

def _async_cutoff_categories(categories, i, rows, mutations):
    ana = Analyzer(.05, 60, .05, .95, 0.8, "z_test")
    ana._timeout = i * 1e3
    cur = {p: set() for p in mutations + ["unsolvable", "unstable", "intersect"]}

    for query_row in rows:
        plain_path = query_row[0]
        group_blobs = query_row[2]
        cat, votes = ana.categorize_query(group_blobs)
        if cat == Stability.UNSTABLE:
            cur["unstable"].add(plain_path)
        elif cat == Stability.UNSOLVABLE:
            cur["unsolvable"].add(plain_path)
        for k, p in enumerate(mutations):
            if votes[k] == Stability.UNSTABLE:
                cur[p].add(plain_path)
        if set(votes.values()) == {Stability.UNSTABLE}:
            # if all of the perturbations is unstable
            cur["intersect"].add(plain_path)

    assert(len(cur["intersect"]) <= len(cur["reseed"]))
    categories[i] = cur

def _mp_get_all_cutoff_categories(rows, cutoffs, mutations):
    manager = mp.Manager()
    pool = mp.Pool(processes=8)
    categories = manager.dict()

    for i in cutoffs:
        # print(i)
        # _async_cutoff_categories(categories, i, rows, mutations)
        pool.apply_async(_async_cutoff_categories, 
                         args=(categories, i, rows, mutations,))
    pool.close()
    pool.join()
    return categories

def _plot_pert_diff(rows, sp):
    mutations = [str(p) for p in MAIN_EXP.enabled_muts]
    cutoffs = np.arange(10, 61, 0.5)

    top = 0
    total = len(rows)

    categories = _mp_get_all_cutoff_categories(rows, cutoffs, mutations)
    keys = ["unstable"] + mutations + ["unsolvable", "intersect"]
    points = {p:[] for p in keys}

    for j in cutoffs:
        for k, v in categories[j].items():
            points[k].append(percentage(len(v), total))

    for k in points:
        if k == "unsolvable":
            continue
        l = MUTATION_LABELS[k] if k in MUTATION_LABELS else k
        if k == "unstable":
            l = r"\texttt{unstable}" + "(all methods)"
        sp.plot(cutoffs, points[k], label=l, color=MUTATION_COLORS[k], linewidth=1.5)
        top = max(top, max(points[k]))

    sp.set_xlim(left=min(cutoffs), right=60)
    sp.set_ylim(bottom=0)
    sp.set_xticks([10, 20, 30, 40, 50, 60])

def plot_appendix_pert_diff():
    rc, cc = 2, 4

    for proj in tqdm(MAIN_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(MAIN_Z3_SOLVERS):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_pert_diff(rows, sp)
            sp.legend()
            sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()

        plt.savefig(f"fig/pert_diff/{proj.name}.pdf")
        plt.close()

def plot_paper_pert_diff():
    figure, axis = plt.subplots(1, 2)
    figure.set_size_inches(7, 4)
    
    solver = Z3_4_12_1
    for index, proj in enumerate([D_KOMODO, D_FVBKV]):
        sp = axis[index]
        rows = load_exp_sums(proj, True, [solver])[solver]
        _plot_pert_diff(rows, sp)
        sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        sp.legend()

    # proj = D_FVBKV
    # summaries = load_exp_sums(proj, True)
    # for index, solver in enumerate([proj.artifact_solver, Z3_4_12_1]):
    #     sp = axis[1][index]
    #     rows = summaries[solver]
    #     _plot_pert_diff(rows, sp)
    #     sp.set_ylim(top=3.5)
    #     sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
    # axis[1][0].legend()

    figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME)
    plt.tight_layout()
    plt.savefig(f"fig/pert_diff/pert_paper.pdf")
    plt.close()

# def _pert_cutoff(proj, sp):
def _get_data_time_cutoff(rows, cutoffs, steps):
    mutations = [str(p) for p in MAIN_EXP.enabled_muts]

    categories = _mp_get_all_cutoff_categories(rows, cutoffs, mutations)
    total = len(rows)
    unstables = [percentage(len(categories[i]["unstable"]), total) for i in cutoffs]
    unsolvables = [percentage(len(categories[i]["unsolvable"]), total) for i in cutoffs]
    
    diffs = [[] for _ in steps]
    for j, step in enumerate(steps):
        changes = []
        for i in cutoffs:
            if i + step > cutoffs[-1]:
                continue
            curr = categories[i]
            next = categories[i+step]
            changes.append(percentage(len(curr["unstable"].intersection(next["unstable"])), total))
        diffs[j] = changes
    
    # print("diffs = ", diffs)
    # print("untables = ", untables)
    # print("unsolvables = ", unsolvables)
    return diffs, unstables, unsolvables

def _plot_ext_cutoff(rows, sp, max_time, steps=[]):
    cutoffs = [i for i in range(10, max_time+1, 1)]

    # name = proj.name
    diffs, unstables, unsolvables = _get_data_time_cutoff(rows, cutoffs, steps)
    sp.plot(cutoffs, unsolvables,
            label=r"\texttt{unsolvable}",color=MUTATION_COLORS["unsolvable"], linewidth=1.5)
    sp.plot(cutoffs, unstables,
            label=r"\texttt{unstable}" + "(+0s)", color=MUTATION_COLORS["unstable"], linewidth=1.5)
    step_colors = ["#A6BDD7", "#817066", "#F6768E"]
    for j, step in enumerate(steps):
        changes = diffs[j]
        sp.plot(cutoffs[:len(changes)], changes,
                label= r"\texttt{unstable}" + f"(+{step}s)",  linestyle='--', color=step_colors[j], linewidth=1.5)
        sp.vlines(cutoffs[-1]-step,
                ymin=0, ymax=changes[-1], linestyle='--', color=step_colors[j], linewidth=1.5)

    sp.set_xlim(left=min(cutoffs), right=max_time)
    sp.set_ylim(bottom=0)
    sp.set_xticks([10, 30, 60, 90, 120, 150])

def plot_appendix_ext_cutoff():
    rc, cc = 3, 2
    figure, axis = plt.subplots(rc, cc)
    solver = Z3_4_12_1
    index = 0
    figure.set_size_inches(15, 12)

    for proj in tqdm(MAIN_PROJS):
        summaries = load_exp_sums(proj, True)
        sp = axis[int(index/cc)][int(index%cc)]
        rows = summaries[solver]
        _plot_ext_cutoff(rows, sp, 150, [10, 30, 60])
        sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        sp.legend(ncol=3)
        index += 1

    figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME) 
        
    plt.tight_layout()
    plt.savefig(f"fig/time_cutoff/time_ext.pdf")
    plt.close()

def plot_paper_ext_cutoff():
    figure, axis = plt.subplots(2, 1)
    figure.set_size_inches(7, 6)
    solver = Z3_4_12_1
    for index, proj in enumerate([D_KOMODO, D_FVBKV]):
        sp = axis[index]
        rows = load_exp_sums(proj, True)[solver]
        _plot_ext_cutoff(rows, sp, 150, [10, 30, 60])
        sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        sp.set_ylim(bottom=0, top=8)
    
    axis[1].legend()
    figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME) 
    plt.tight_layout()
    plt.savefig(f"fig/time_cutoff/cutoff_paper.pdf")
    plt.close()

def create_benchmark(projs=MAIN_PROJS):
    import random

    benchmark_path = "data/benchmark"
    
    unstable_core_path = f"{benchmark_path}/unstable_core"
    unstable_ext_path = f"{benchmark_path}/unstable_ext"
    stable_core_path = f"{benchmark_path}/stable_core"
    stable_ext_path = f"{benchmark_path}/stable_ext"

    os.system(f"mkdir -p {unstable_core_path}")
    os.system(f"mkdir -p {unstable_ext_path}")
    os.system(f"mkdir -p {stable_core_path}")
    os.system(f"mkdir -p {stable_ext_path}")
        
    ana = Z_TEST_60

    for proj in projs:
        print(proj.get_project_name())
        unss = []
        summaries = load_exp_sums(proj, solvers=[proj.artifact_solver, Z3_4_12_1])
        for solver in [proj.artifact_solver, Z3_4_12_1]:
            rows = summaries[solver]
            items = ana.categorize_queries(rows)
            unss.append(items)
        core = unss[0]['unstable'].intersection(unss[1]['unstable'])
        ext = unss[1]['unstable'] - core
        print("unstable core: ", len(core))
        print("unstable ext:", len(ext))
        
        stables = items['stable']
        
        # stable ext
        maybes = set()
        # stable core
        stable_core = set()

        for query_row in rows:
            query_path = query_row[0]
            if query_path not in stables:
                continue
            group_blobs = query_row[2]

            std = 0
            combined = np.concatenate((group_blobs[:,1][0], group_blobs[:,1][1], group_blobs[:,1][2]))
            std_combined = np.std(combined) / 1000

            # going thru each perturb
            for i in range(3):
                times = group_blobs[:,1][i]
                times = np.clip(times, 0, 6e4) / 1000
                std = max(std, np.std(times))

            # std = np.std(np.clip(group_blobs[0][1], 0, 61e3) / 1000)
            if std > 6:
                maybes.add(query_path)
                    # maybes[query_path] = np.std(bs)
            # std of all groups is less than 1
            elif std_combined < 1:
                stable_core.add(query_path)

        # randomly sample from stable_core:
        random.seed(4)
        sampled_core = random.sample(sorted(list(stable_core)), 30)

        print("stable core:", len(sampled_core), f" (original: {len(stable_core)})")
        print("stable ext:", len(maybes))
        
        # add all unstable core 
        for filename in core:
            shutil.copyfile(filename, f"{unstable_core_path}/{proj.get_project_name()}-{filename.split('/')[2]}")
#           print("added: ", filename)

        # add all unstable ext
        for filename in ext:
            shutil.copyfile(filename, f"{unstable_ext_path}/{proj.get_project_name()}-{filename.split('/')[2]}")

        # add all stable core
        for filename in sampled_core:
            shutil.copyfile(filename, f"{stable_core_path}/{proj.get_project_name()}-{filename.split('/')[2]}")

        # add all stable ext
        for filename in maybes:
            shutil.copyfile(filename, f"{stable_ext_path}/{proj.get_project_name()}-{filename.split('/')[2]}")


skip = {"attest.vad",
"attest_helpers.vad",
"attest_input.vad",
"sha/sha-Seqs.s.dfy",
"sha/sha-bit-vector-lemmas.i.dfy",
"sha/sha-hmac-helpers.i.dfy",
"sha/sha-hmac.vad",
"sha/sha-hmac_common.s.dfy",
"sha/sha-memory-helpers.i.dfy",
"sha/sha-sha256-api.vad",
"sha/sha-sha256-block-data-order.vad",
"sha/sha-sha256-body-00-15.vad",
"sha/sha-sha256-body-16-xx.vad",
"sha/sha-sha256-body-helpers.vad",
"sha/sha-sha256-helpers.i.dfy",
"sha/sha-sha256-invariants.i.dfy",
"sha/sha-sha256-one-block.vad",
"sha/sha-sha256.i.dfy",
"sha/sha-sha256.s.dfy",
"sha/sha-sha_common.s.dfy",
"verify.vad",
"verify_input.vad",
"words_and_bytes.i.dfy",
"words_and_bytes.s.dfy",
"words_and_bytes_isolated.i.dfy"}

def locality_analysis(proj):
    summaries = load_exp_sums(proj, solvers=[Z3_4_12_1])
    c = Z_TEST_60
    counts = {}
    summary = summaries[Z3_4_12_1]
    fnames = set()
    for row in summary:
        group_blobs = row[2]
        fname = row[0].split(".dfy")[0][32:]

        if "secprop-" in fname:
            fname = "secprop/" + fname[8:]
        elif "sha-" in fname:
            fname = "sha/" + fname[:]

        if fname.endswith(".gen"):
            fname = fname.replace(".gen", ".vad")
        else:
            fname = fname + ".dfy"
        fnames.add(fname)
        if fname in skip :
            continue

        if fname not in counts:
            counts[fname] = [0, 0]
        
        counts[fname][0] += 1
        if c.categorize_query(group_blobs)[0] == Stability.UNSTABLE:
            counts[fname][1] += 1
    total, us = 0, 0
    for fname in counts:
        # print(fname, counts[fname][0])
        total += counts[fname][0]
        us += counts[fname][1]
    print(us, total, us * 100 / total)
    # print(counts)

def plot_appendix_sizes():
    # figure, axis = setup_fig(1, 2)
    x_max = 0
    for proj in [D_LVBKV, D_FVBKV, D_KOMODO, FS_DICE, FS_VWASM, S_KOMODO]:
        clean_dir = proj.clean_dir
        paths = list_smt2_files(clean_dir)
        sizes = []
        for path in paths:
            sizes.append(os.path.getsize(path) / 1024 / 1024)
        n = len(sizes)
        label = PROJECT_LABELS[proj.name]
        color = PROJECT_COLORS[proj.name]
        x_max = max(x_max, np.max(sizes))
        plt.plot(np.sort(sizes), np.arange(n), label=label, color=color, linewidth=1.5)
        plt.plot(np.max(sizes), n, marker="o", color=color, markersize=5)
        align = "left"
        if proj == D_FVBKV:
            align = "right"
        plt.text(np.max(sizes)-0.2, n+80, label,  fontname=FNAME, horizontalalignment=align)

    # plt.legend()
    # plt.xscale("log")
    plt.ylim(bottom=0)
    plt.xlim(left=0, right=x_max)
    plt.ylabel("cumulative query count",  fontsize=FSIZE, fontname=FNAME)
    plt.xlabel("size (MB)",  fontsize=FSIZE, fontname=FNAME) 

    plt.tight_layout()
    plt.savefig("fig/sizes.pdf")

def _plot_srs(exp, rows, sp):
    dps = np.zeros((len(rows), 3))
    for query_row in rows:
        group_blobs = query_row[2]

        for k in range(len(group_blobs)):
            success = count_within_timeout(group_blobs[k], RCode.UNSAT, timeout=6e4)
            dps[rows.index(query_row), k] = percentage(success, 61)
    end = 0
    mutations = [str(p) for p in exp.enabled_muts]
    
    for i, m in enumerate(mutations):
        label = MUTATION_LABELS[m]
        color = MUTATION_COLORS[m]
        xs, ys = get_cdf_pts(dps[:,i])
        end = max(ys[np.argmax(xs > 99)], end)
        sp.plot(xs, ys, label=label, color=color)
    sp.legend()
    sp.set_xlim(left=0, right=100)
    sp.set_ylim(bottom=0, top=end)

def plot_appendix_srs():
    # cc = 2
    # figure, axis = plt.subplots(6, 1, figsize=(7, 24))
    # figure.set_size_inches(7, 4)
    rc, cc = 2, 4

    for proj in tqdm(MAIN_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(MAIN_Z3_SOLVERS):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_srs(MAIN_EXP, rows, sp)
            sp.set_title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel(r"mutant success rate ($\%$)", fontsize=FSIZE, fontname=FNAME)
        figure.supylabel(r"cumulative proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
        
        plt.tight_layout()
        plt.savefig(f"fig/sr_cdf/{proj.name}.pdf")
        plt.close()

# def count_timeouts(proj):
#     summaries = load_solver_summaries(proj, skip_unknowns=True)
#     c = Analyzer(method="z_test")
#     c.timeout = 15e4

#     summary = summaries[Z3_4_12_1]
#     counts = []
#     for row in summary:
#         group_blobs = row[2]
#         # combined = np.concatenate((group_blobs[:,1][0], group_blobs[0,:,1:][1], group_blobs[0,:,1:][2]))
#         if c.categorize_query(group_blobs) != Stability.UNSTABLE:
#             continue

#         combined = np.hstack((group_blobs[0,:,:], group_blobs[1,:,1:], group_blobs[2,:,1:]))
#         combined = combined.T

#         to = 0
#         fs = 0
#         for (res, time) in combined:
#             if time >= 15e4:
#                 to += 1
#                 fs += 1
#             elif res != RCode.UNSAT.value:
#                 fs += 1
#         if fs == 0:
#             continue
#         # if to == 0:
#         #     print(combined.T)
#         counts.append(percentage(to, fs))
#     print(np.mean(counts))
#         # success = blob[0] == rcode.value
#         # none_timeout = blob[1] < timeout
#         # success = np.sum(np.logical_and(success, none_timeout))
            
#         # count_within_timeout(group_blobs[i], RCode.UNSAT, timeout=6e4)

# def compare_vbkvs(linear, dynamic):
#     dfiles, lfiles = set(), set()
#     for k, v in FILE_MAP.items():
#         dfiles |= set(v[0])
#         lfiles |= set(v[1])
#     # print(len(lfiles))
#     # print(len(dfiles))

#     ana = Analyzer("z_test")
#     ana.timeout = 61e4
#     # th.r_solvable = 20
#     # th.r_stable = 80

#     l_filtered = set()
#     for query in linear.samples[Z3_4_12_1]:
#         for f in lfiles:
#             if "-" + f in query:
#                 l_filtered.add(query)
#     d_filtered = set()
#     for query in dynamic.samples[Z3_4_12_1]:
#         for f in dfiles:
#             if "-" + f in query:
#                 d_filtered.add(query)
#                 break

#     print(len(l_filtered))
#     print(len(d_filtered))

#     # data = np.zeros((4, len(Stability)))

#     l_summary = load_solver_summary(linear, Z3_4_12_1, get_unknowns(linear))
#     # l_categories = categorize_queries(l_summary, ana)
#     pts = []
#     xs = []
#     ys = []
#     maybes = 0

#     for query_row in l_summary:
#         # if query_row[0] not in l_filtered:
#         #     continue
#         group_blobs = query_row[2]
#         res = ana.categorize_query(group_blobs, None)

#         if res != Stability.STABLE:
#             continue
        
#         mean = 0
#         std = 0
        
#         for i in range(3):
#             times = group_blobs[:,1][i]
#             times = np.clip(times, 0, 6e4) / 1000
#             cur = np.std(times)
#             if std < cur:
#                 mean = np.mean(times)
#                 std = cur
        
#         if std < 1 and mean > 15:
#             maybes += 1
        
#         xs.append(mean)
#         ys.append(std)

#     plt.scatter(xs, ys, label="linear", s=2, alpha=0.5)
#     print(maybes)

#     maybes = 0

#     d_summary = load_solver_summary(dynamic, Z3_4_12_1, get_unknowns(dynamic))

#     xs = []
#     ys = []
#     for query_row in d_summary:
#         # if query_row[0] not in d_filtered:
#         #     continue
#         group_blobs = query_row[2]
#         res = ana.categorize_query(group_blobs, None)

#         if res != Stability.STABLE:
#             continue
        
#         mean = 0
#         std = 0
        
#         for i in range(3):
#             times = group_blobs[:,1][i]
#             times = np.clip(times, 0, 6e4) / 1000
#             cur = np.std(times)
#             if std < cur:
#                 mean = np.mean(times)
#                 std = cur
        
#         if std < 1 and mean > 15:
#             maybes += 1
        
#         xs.append(mean)
#         ys.append(std)

#     plt.scatter(xs, ys, label="dynamic", marker="x", s=2)
#     plt.xlim(left=1)
#     print(maybes)
    
#     # print(len(d_summary))
#     # pts = []
#     # # d_categories = categorize_queries(d_summary, ana)
#     # for query_row in d_summary:
#     #     if query_row[0] not in d_filtered:
#     #         continue
#     #     group_blobs = query_row[2] 
#     #     if group_blobs[0][0][0] == RCode.UNSAT.value:
#     #         pts.append(group_blobs[0][1][0] / 1000)
        
#     # xs, ys = get_cdf_pts(pts)
#     # # ys = np.flip(ys)
#     # plt.plot(xs, ys, label="dynamic")
#     # plt.xlim(left=5)
#     # plt.ylim(bottom=98, top=100)

#     plt.legend()
#     plt.tight_layout()
#     plt.savefig("fig/compare.pdf")

def plot_paper_figs():
    plot_paper_overall()
    plot_paper_ext_cutoff()
    plot_paper_pert_diff()
    plot_paper_time_std()
    plot_paper_time_scatter()

def plot_appendix_figs():
    plot_appendix_ext_cutoff()
    plot_appendix_pert_diff()
    plot_appendix_time_std()
    plot_appendix_time_scatter()
#   plot_appendix_sizes()
    plot_appendix_srs()


### unsat core figures:

def get_unsat_core_stats(project):
    # open "data/unsat_core.db" and get rows 
    con, cur = get_cursor("data/unsat_core.db")
    # for each row, get the 1.) unsat core path 2.) original query path 3.) original query time 4.) unsat core time 5.) original query size 6.) unsat core size
    get_size = cur.execute(f"SELECT query_path FROM {project.name.upper()}_MIN_ASSERTS_z3_4_8_5")
    project_name_caps = ""
    if "_z3" in project.name:
        project_name_caps = project.name[:-3].upper()
    else:
        project_name_caps = project.name.upper()
    project_name = project_name_caps.lower()
    original_table_name = f"{project_name_caps}_z3_4_8_5"
    size_res = []
    for query_path in get_size.fetchall():
        query_name = query_path[0].split("/")[-1]
        core_path = query_path[0]
        original_path = project.original_root + query_name
        original_size = os.path.getsize(original_path)
        unsat_size = os.path.getsize(core_path)
        size_res.append(unsat_size / original_size)
    for check in size_res:
        if check > 1 or check <= 0: print(f"error: {check}")

    get_time = cur.execute(f"SELECT query_path, elapsed_milli FROM {project.name.upper()}_MIN_ASSERTS_z3_4_8_5 WHERE result_code = 'unsat' ")
    mariposa_con, mariposa_cur = get_cursor("data/mariposa.db")
    mariposa_cur.execute(f"SELECT query_path, elapsed_milli FROM {original_table_name} WHERE query_path like 'data%' ")
    time_dict = dict(mariposa_cur.fetchall())
    time_res = []
    for query_path, unsat_time in get_time.fetchall():
        query_name = query_path.split("/")[-1]
        core_path = query_path
        original_path = f"data/{project.name}_clean/{query_name}"
        original_time = time_dict[original_path]
        time_res.append(unsat_time / original_time)

    # return a tuple of lists ([size ratio list], [time ratio list]) for time and size ratio graphs
    return [size_res, time_res]

def plot_size_reduction_graph():
    fig, ax = plt.subplots()
    ax.set_xlim(left=0.0, right=1.0)
    ax.set_title('all projects size ratio cdf')
    ax.set_ylabel("cumulative proportion of queries (\%)")
    ax.set_xlabel("size ratio (minimized asserts query filesize / original query filesize)")
    for project in PROJECTS:
        project_name_caps = ""
        if "_z3" in project.name:
            project_name_caps = project.name[:-3].upper()
        else:
            project_name_caps = project.name.upper()
        size_res = get_unsat_core_stats(project)[0]
        xs, ys = get_cdf_pts(size_res)
        label = PROJECT_LABELS[project_name_caps]
        color = PROJECT_COLORS[project_name_caps]
        ax.plot(xs, ys, label=label, color=color, linewidth=0.5)
        ax.plot(np.max(xs), np.max(ys), marker="o", color=color, markersize=2)
    plt.legend(loc='best')
    plt.savefig(f"fig/unsat_core/all_size.pdf")
    plt.close()
    


def plot_time_reduction_graph_zoomed():
    fig, ax = plt.subplots()
    ax.set_xlim(left=0.0, right=2.0)
    ax.set_title('all projects runtime ratio cdf zoomed')
    ax.set_ylabel("cumulative proportion of queries (\%)")
    ax.set_xlabel("runtime ratio (minimized asserts query runtime / original query runtime)")
#   ax.set_xscale("log")
#   ax.set_yscale("log")
    for project in PROJECTS:
        project_name_caps = ""
        if "_z3" in project.name:
            project_name_caps = project.name[:-3].upper()
        else:
            project_name_caps = project.name.upper()
        time_res = get_unsat_core_stats(project)[1]
        xs, ys = get_cdf_pts(time_res)
        label = PROJECT_LABELS[project_name_caps]
        color = PROJECT_COLORS[project_name_caps]
        ax.plot(xs, ys, label=label, color=color, linewidth=0.5)
        ax.plot(np.max(xs), np.max(ys), marker="o", color=color, markersize=2)
    plt.legend(loc='best')
    plt.savefig(f"fig/unsat_core/all_time_zoomed.pdf")
    plt.close()


def plot_time_reduction_graph():
    fig, ax = plt.subplots()
    ax.set_title('all projects runtime ratio cdf')
    ax.set_ylabel("cumulative proportion of queries (\%)")
    ax.set_xlabel("runtime ratio (minimized asserts query runtime / original query runtime)")
    ax.set_xscale("log")
    for project in PROJECTS:
        project_name_caps = ""
        if "_z3" in project.name:
            project_name_caps = project.name[:-3].upper()
        else:
            project_name_caps = project.name.upper()
        time_res = get_unsat_core_stats(project)[1]
        xs, ys = get_cdf_pts(time_res)
        label = PROJECT_LABELS[project_name_caps]
        color = PROJECT_COLORS[project_name_caps]
        ax.plot(xs, ys, label=label, color=color, linewidth=0.5)
        ax.plot(np.max(xs), np.max(ys), marker="o", color=color, markersize=2)
    plt.legend(loc='best')
    plt.savefig(f"fig/unsat_core/all_time.pdf")
    plt.close()
    

def get_size_vs_time_data(db_path, table_name, query_root=""):
    con, cur = get_cursor(db_path)
    res = cur.execute(f"SELECT query_path, elapsed_milli FROM {table_name} WHERE result_code = 'unsat' and query_path like 'data%' ")
    pair = ([], [])
    for query_path, time in res.fetchall():
        query_name = query_path.split("/")[-1]
        file_size = os.path.getsize(query_root + query_name)
        pair[0].append(file_size)
        pair[1].append(time)
    return pair

def plot_size_vs_time_correlations():
    fig, ax = plt.subplots()
    ax.set_title('all projects size vs time correlations')
    ax.set_xlabel("file size (MB)")
    ax.set_ylabel("time (seconds)")
    for i, project in enumerate(PROJECTS):
        project_name_caps = ""
        if "_z3" in project.name:
            project_name_caps = project.name[:-3].upper()
        else:
            project_name_caps = project.name.upper()
        project_name = project_name_caps.lower()
        original_table_name = f"{project_name_caps}_z3_4_8_5"
        xs, ys = get_size_vs_time_data("data/mariposa.db", original_table_name, project.original_root)
        xs = [x/1000000 for x in xs]
        ys = [y/1000 for y in ys]
        label = PROJECT_LABELS[project_name_caps]
        color = PROJECT_COLORS[project_name_caps]
        # scatter plot xs and ys
        ax.scatter(xs, ys, label=label, color=color, s=1)
    ax.legend(loc="best")
    plt.savefig(f"fig/unsat_core/size_vs_time.pdf")
    plt.close()

import statsmodels.formula.api as smf
import pandas as pd
def plot_size_vs_time_regression():
    fig, ax = plt.subplots()
    ax.set_title('all projects size vs time correlations w/ regression')
    ax.set_xlabel("file size (MB)")
    ax.set_ylabel("time (seconds)")
    ax.set_xlim(left=-1,right=30)
    xss = []
    yss = []
    for i, project in enumerate(PROJECTS):
        project_name_caps = ""
        if "_z3" in project.name:
            project_name_caps = project.name[:-3].upper()
        else:
            project_name_caps = project.name.upper()
        project_name = project_name_caps.lower()
        original_table_name = f"{project_name_caps}_z3_4_8_5"
        xs, ys = get_size_vs_time_data("data/mariposa.db", original_table_name, project.original_root)
        xs = [x/1000000 for x in xs]
        ys = [y/1000 for y in ys]
        xss += xs; yss += ys
        label = PROJECT_LABELS[project_name_caps]
        color = PROJECT_COLORS[project_name_caps]
        # scatter plot xs and ys
        ax.scatter(xs, ys, label=label, color=color, s=.5, alpha=.5)
    # regression on xss, yss
    xss = np.array(xss); yss = np.array(yss)
    model = smf.quantreg('time ~ size', pd.DataFrame({'size':xss, 'time':yss})).fit(q=.001)
    y_line = lambda a, b: a + b * xss
    y = y_line(model.params['Intercept'],
               model.params['size'])
    y_another_line = y_line(2+ model.params['Intercept'],
               model.params['size'])
    # count number of points falling below y_another_line
    count = 0
    for i in range(len(xss)):
        if yss[i] < y_another_line[i]:
            count += 1
    print(f"percentage of queries inside 2 seconds lines: {count} / {len(xss)}:")
    print(count / len(xss))
    print(model.summary())
    ax.plot(xss, y, color="black", lw=.5, label=f".001 (slope = {model.params['size']})")
    ax.plot(xss, y_another_line, color="red", lw=.5, label=".001 line + 2 secs")
    ax.legend(loc="best")
    plt.savefig(f"fig/unsat_core/size_vs_time_regression.pdf")
    plt.close()

def plot_size_vs_time_regression_unsat_core():
    fig, ax = plt.subplots()
    ax.set_title('all projects min asserts size vs time correlations w/ regression')
    ax.set_xlabel("file size (MB)")
    ax.set_ylabel("time (seconds)")
    ax.set_xlim(left=-.5,right=13)
    xss = []
    yss = []
    for i, project in enumerate(PROJECTS):
        project_name_caps = ""
        if "_z3" in project.name:
            project_name_caps = project.name[:-3].upper()
        else:
            project_name_caps = project.name.upper()
        project_name = project_name_caps.lower()
        original_table_name = f"{project.name.upper()}_MIN_ASSERTS_z3_4_8_5"
        xs, ys = get_size_vs_time_data("data/unsat_core.db", original_table_name, project.min_assert_root)
        xs = [x/1000000 for x in xs]
        ys = [y/1000 for y in ys]
        xss += xs; yss += ys
        label = PROJECT_LABELS[project_name_caps]
        color = PROJECT_COLORS[project_name_caps]
        # scatter plot xs and ys
        ax.scatter(xs, ys, label=label, color=color, s=.5, alpha=.5)
    # regression on xss, yss
    xss = np.array(xss); yss = np.array(yss)
    model = smf.quantreg('time ~ size', pd.DataFrame({'size':xss, 'time':yss})).fit(q=.001)
    y_line = lambda a, b: a + b * xss
    y = y_line(model.params['Intercept'],
               model.params['size'])
    y_another_line = y_line(2+ model.params['Intercept'],
               model.params['size'])
    # count number of points falling below y_another_line
    count = 0
    for i in range(len(xss)):
        if yss[i] < y_another_line[i]:
            count += 1
    print(f"percentage of queries inside 2 seconds lines: {count} / {len(xss)}:")
    print(count / len(xss))
    print(model.summary())
    ax.plot(xss, y, color="black", lw=.5, label=f".001 (slope = {model.params['size']})")
    ax.plot(xss, y_another_line, color="red", lw=.5, label=".001 line + 2 secs")
    ax.legend(loc="best")
    plt.savefig(f"fig/unsat_core/size_vs_time_regression_unsat_core.pdf")
    ax.set_ylim(bottom=-1,top=40)
    plt.savefig(f"fig/unsat_core/size_vs_time_regression_unsat_core_zoomed.pdf")
    plt.close()

def plot_pie_chart():
    fig, axs = plt.subplots(nrows=2, ncols=3, figsize=(30,10))
    for i, project in enumerate(PROJECTS):
        og_unsat = set()
        og_timeout = set()
        og_unknown = set()
        min_unsat = set()
        min_timeout = set()
        min_unknown = set()
        original_queries_table = f"{project.name.upper()}_UNSAT_CORE_z3_4_8_5"
        min_queries_table = f"{project.name.upper()}_MIN_ASSERTS_z3_4_8_5"
        con, cur = get_cursor("data/unsat_core.db")
        res = cur.execute(f"SELECT query_path, result_code FROM {original_queries_table}")
        for query_path, result in res:
            query = query_path.split("/")[-1]
            if result == "unsat": og_unsat.add(query)
            elif result == "timeout": og_timeout.add(query)
            elif result == "unknown": og_unknown.add(query)
        res = cur.execute(f"SELECT query_path, result_code FROM {min_queries_table}")
        for query_path, result in res:
            query = query_path.split("/")[-1]
            if result == "unsat": min_unsat.add(query)
            elif result == "timeout": min_timeout.add(query)
            elif result == "unknown": min_unknown.add(query)
        print(project.name)
        values = [len(og_timeout), len(og_unknown), len(min_timeout), len(min_unknown), len(min_unsat)]
        val_sum = np.sum(values)
        percs = [ "{:.1%}".format(x / val_sum ) for x in values]
        print(percs)
        labels = ["original query timeout ", "original query unknown", "original query unsat and minimized query timeout", "original query unsat and minimized query unknown", "original query unsat and\nminimized query unsat"]
        labels = [f"{label} (${percs[i][:-1]}\%$)" for i, label in enumerate(labels)]
        explode = [0.2,0.2,0,0,0]
        colors = [
            "#803E75", # Strong Purple
            "#FF6800", # Vivid Orange
            "#A6BDD7", # Very Light Blue
            "#FFB300", # Vivid Yellow
            "#C10020", # Vivid Red
            "#817066", # Medium Gray
        ]
        # exclude labels[i], percs[i], explode[i], and values[i] if values[i] == 0
        j = 0
        while j < len(values):
            if values[j] == 0:
                labels.pop(j)
                percs.pop(j)
                values.pop(j)
                explode.pop(j)
                colors.pop(j)
            else: j+=1
        ax = axs[i//3][i%3]
        ax.set_title(f"{project.name} original and min query results distribution")

        kw = dict(arrowprops=dict(arrowstyle="-"),
                  zorder=0, va="center")

#       for i, p in enumerate(wedges):
#           ang = (p.theta2 - p.theta1)/2. + p.theta1
#           y = np.sin(np.deg2rad(ang))
#           x = np.cos(np.deg2rad(ang))
#           horizontalalignment = {-1: "right", 1: "left"}[int(np.sign(x))]
#           connectionstyle = f"angle,angleA=0,angleB={ang}"
#           kw["arrowprops"].update({"connectionstyle": connectionstyle})
#           ax.annotate(labels[i], xy=(x, y), # xytext=(1.9*np.sign(x), 1.9*y), 
#                       horizontalalignment=horizontalalignment, **kw, fontsize=9)

        ax.pie(values, labels = labels, explode = explode, textprops={'fontsize': 6}, labeldistance=1.25, colors=colors)
    plt.savefig(f"fig/unsat_core/all_pie.pdf")

import plotly.express as px
from plotly.subplots import make_subplots
import plotly.graph_objects as go

def plot_pie_chart_plotly():
    fig = make_subplots(rows=2,cols=3, specs=[[{"type":"domain"} for _ in range(3)] for _ in range(2)], subplot_titles=[project.name for project in PROJECTS])
    for i, project in enumerate(PROJECTS):
        og_unsat = set()
        og_timeout = set()
        og_unknown = set()
        min_unsat = set()
        min_timeout = set()
        min_unknown = set()
        original_queries_table = f"{project.name.upper()}_UNSAT_CORE_z3_4_8_5"
        min_queries_table = f"{project.name.upper()}_MIN_ASSERTS_z3_4_8_5"
        con, cur = get_cursor("data/unsat_core.db")
        res = cur.execute(f"SELECT query_path, result_code FROM {original_queries_table}")
        for query_path, result in res:
            query = query_path.split("/")[-1]
            if result == "unsat": og_unsat.add(query)
            elif result == "timeout": og_timeout.add(query)
            elif result == "unknown": og_unknown.add(query)
        res = cur.execute(f"SELECT query_path, result_code FROM {min_queries_table}")
        for query_path, result in res:
            query = query_path.split("/")[-1]
            if result == "unsat": min_unsat.add(query)
            elif result == "timeout": min_timeout.add(query)
            elif result == "unknown": min_unknown.add(query)
        print(project.name)
        values = [len(og_timeout), len(og_unknown), len(min_timeout), len(min_unknown), len(min_unsat)]
        val_sum = np.sum(values)
        percs = [ "{:.1%}".format(x / val_sum ) for x in values]
        print(percs)
        labels = ["original query timeout", "original query unknown", "original query unsat and min query timeout", "original query unsat and min query unknown", "original query unsat and min query unsat"]
#       explode = [0.2,0.2,0,0,0]
        colors = [
            "#803E75", # Strong Purple
            "#FF6800", # Vivid Orange
            "#A6BDD7", # Very Light Blue
            "#FFB300", # Vivid Yellow
            "#C10020", # Vivid Red
            "#817066", # Medium Gray
        ]
        # exclude labels[i], percs[i], explode[i], and values[i] if values[i] == 0
        j = 0
        while j < len(values):
            if values[j] == 0:
                labels.pop(j)
                percs.pop(j)
                values.pop(j)
#               explode.pop(j)
                colors.pop(j)
            else: 
                labels[j] += f" ({values[j]})"
                j+=1
        fig.add_trace(go.Pie(labels=labels, values=values, textinfo='label+percent', 
                              showlegend=False, 
                             marker=dict(colors=colors)), row=(i)//3+1, col=(i)%3+1)
    # move titles down
    fig.update_annotations(yshift=-300)
    fig.update_layout(height=900, width=1350)
    # following 3 lines are to avoid "Loading Mathjax" issue
    fig.write_image("fig/unsat_core/all_pie_plotly.pdf")
    import time
    time.sleep(2)
    fig.write_image("fig/unsat_core/all_pie_plotly.pdf")


def generate_table():
    for project in PROJECTS:
        og_unsat = set()
        og_timeout = set()
        og_unknown = set()
        min_unsat = set()
        min_timeout = set()
        min_unknown = set()
        original_queries_table = f"{project.name.upper()}_UNSAT_CORE_z3_4_8_5"
        min_queries_table = f"{project.name.upper()}_MIN_ASSERTS_z3_4_8_5"
        con, cur = get_cursor("data/unsat_core.db")
        res = cur.execute(f"SELECT query_path, result_code FROM {original_queries_table}")
        for query_path, result in res:
            query = query_path.split("/")[-1]
            if result == "unsat": og_unsat.add(query)
            elif result == "timeout": og_timeout.add(query)
            elif result == "unknown": og_unknown.add(query)
        res = cur.execute(f"SELECT query_path, result_code FROM {min_queries_table}")
        for query_path, result in res:
            query = query_path.split("/")[-1]
            if result == "unsat": min_unsat.add(query)
            elif result == "timeout": min_timeout.add(query)
            elif result == "unknown": min_unknown.add(query)
        print(project.name)
        print(f"""original unsat: {len(og_unsat)}
original timeout: {len(og_timeout)}
original unknown: {len(og_unknown)}
min unsat: {len(min_unsat)}
min timeout: {len(min_timeout)}
min unknown: {len(min_unknown)}
               """)

def stem_file_paths(items):
    new_items = {}
    all = set()
    for cat in Stability:
        new_items[cat] = set()
        for query in items[cat]:
            new_items[cat].add(query.split("/")[-1])
        all.update(new_items[cat])
    return new_items

def migration(items1, items2, cats):
    row = [""]

    for c2 in cats:
       row.append(f"{c2.name}({len(items2[c2])})") 
    
    rows = [row]
    
    for c1 in cats:
        row = [f"{c1.name}({len(items1[c1])})"]
        for c2 in cats:
            row.append(len(items1[c1].intersection(items2[c2])))
        rows.append(row)
    print(tabulate(rows, headers="firstrow", tablefmt="github"))

def unsat_core_migration():
    cats = [Stability.UNSTABLE, Stability.UNSOLVABLE, Stability.STABLE, Stability.TALLY]

    uk = get_unknowns(D_KOMODO)
    rows = load_sum_table(D_KOMODO, Z3_4_12_1, MAIN_EXP, uk)
    items = Z_TEST_60.categorize_queries(rows, tally=True)
    items = stem_file_paths(items)
    ps, total = get_category_percentages(items)

    D_KOMODO_UC = c.load_known_project("d_komodo_uc")
    exp = c.load_known_experiment("unsat_core")
    uk = get_unknowns(D_KOMODO_UC, exp)
    rows = load_sum_table(D_KOMODO_UC, Z3_4_12_1, exp, uk)
    items2 = Z_TEST_60.categorize_queries(rows, tally=True)

    items2 = stem_file_paths(items2)
    ps, total = get_category_percentages(items2)
    
    migration(items, items2, cats)

def compose_migration():
    cats = [Stability.UNSTABLE, Stability.UNSOLVABLE, Stability.STABLE, Stability.INCONCLUSIVE]
    proj = D_KOMODO

    # uk = get_unknowns(proj)
    uk = set()
    rows = load_sum_table(proj, Z3_4_12_1, MAIN_EXP, uk)
    items = Z_TEST_60.categorize_queries(rows)
    ps, total = get_category_percentages(items)

    pp_table = [["category", "count", "percentage"]]
    for cat in [Stability.UNSOLVABLE, Stability.UNSTABLE, Stability.INCONCLUSIVE, Stability.STABLE]:
        pp_table.append([cat.value, len(items[cat]), round(ps[cat], 2)])
    print(tabulate(pp_table, tablefmt="github"))

    nrows = dict()
    
    for e in ["compose", "compose2", "compose3"]:
        exp = c.load_known_experiment(e)
        rows = load_sum_table(proj, Z3_4_12_1, exp, uk)
        for row in rows:
            if row[0] not in nrows:
                nrows[row[0]] = []
            nrows[row[0]].append(row)
    nnrows = []

    for k in nrows:
        blob = np.hstack([v[2][0] for v in nrows[k]])
        blob = np.expand_dims(blob, axis=0)
        nnrows.append([k, ["all"], blob])
    items2 = Z_TEST_60.categorize_queries(nnrows)
    ps, total = get_category_percentages(items2)

    pp_table = [["category", "count", "percentage"]]
    for cat in [Stability.UNSOLVABLE, Stability.UNSTABLE, Stability.INCONCLUSIVE, Stability.STABLE]:
        pp_table.append([cat.value, len(items2[cat]), round(ps[cat], 2)])
    print(tabulate(pp_table, tablefmt="github"))
    migration(items2, items, cats)

if __name__ == "__main__":
  plot_paper_figs()
#   plot_appendix_figs()
    # plot_paper_overall()
    # compose_migration()