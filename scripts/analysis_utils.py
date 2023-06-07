from db_utils import *
from vbkv_filemap import *
import shutil

from projects import *
from experiments import *
from plot_utils import *
import matplotlib.pyplot as plt
import multiprocessing as mp

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

def make_title(proj, solver):
    # star = ""
    # if proj.orig_solver == solver:
    #     star = r"$\star$"
    return f"{PROJECT_LABELS[proj.name]} {solver.pstr()}"

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

def percentage(a, b):
    return a * 100 / b

def get_category_percentages(categories):
    percentages = dict()
    total = sum([len(i) for i in categories.values()])
    for c, i in categories.items():
        percentages[c] = percentage(len(i), total)
    return percentages, total

def get_unknowns(proj):
    th = Analyzer("strict")
    th.timeout = 6e4
    summary = load_sum_table(proj, proj.orig_solver)
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
        solvers = Z3_SOLVERS_ALL

    for solver in solvers:
        nrows = load_sum_table(proj, solver, skip=unknowns)
        if nrows is None:
            continue
        summaries[solver] = nrows
    return summaries

def _async_categorize_project(ratios, key, rows):
    ana = Analyzer("z_test")
    ana.timeout = 6e4 # 1 min
    items = ana.categorize_queries(rows)
    ps, _ = get_category_percentages(items)
    ratios[key] = ps

def _mp_categorize_projects(projs, solver_names):
    manager = mp.Manager()
    ratios = manager.dict()

    for proj in projs:
        summaries = load_exp_sums(proj)
        pool = mp.Pool(processes=8)
        for solver in solver_names:
            key = (projs.index(proj), solver_names.index(solver))
            rows = summaries[solver]
            pool.apply_async(_async_categorize_project, 
                            args=(ratios, key, rows,))
        pool.close()
        pool.join()

    category_count = len(Stability)
    data = np.zeros((len(projs), len(solver_names), category_count))

    for key in ratios:
        i, j = key
        data[i][j] = [ratios[key][s] for s in Stability]

    return data

def plot_paper_overall(projs=ALL_PROJS):
    project_names = [proj.name for proj in projs]
    solver_names = [str(s) for s in Z3_SOLVERS_ALL]
    solver_labels = [f"{s.pstr()}\n{s.data[:-3]}" for s in Z3_SOLVERS_ALL]

    data = _mp_categorize_projects(projs, solver_names)
    
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
    #         print(Z3_SOLVERS_ALL[j].pstr(), end=" & ")
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
            if solver_names[i] == str(projs[pi].orig_solver):
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

    ana = Analyzer("z_test")
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
    for proj in tqdm(ALL_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)

        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
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
    ana = Analyzer("z_test")
    ana.timeout = 6e4 # 1 min

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

def _plot_time_std(cfg, rows, sp):
    y_bound = 0
    x_bound = 0
    dps = _get_data_time_std(rows)
    mutations = [str(p) for p in cfg.enabled_muts]

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

    for proj in tqdm(ALL_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
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
    ana = Analyzer("z_test")
    ana.timeout = i * 1e3
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

    for proj in tqdm(ALL_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
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
    # for index, solver in enumerate([proj.orig_solver, Z3_4_12_1]):
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

    for proj in tqdm(ALL_PROJS):
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

def create_benchmark(projs=ALL_PROJS):
    benchmark_path = "data/benchmark"
    
    unstable_core_path = f"{benchmark_path}/unstable_core"
    unstable_ext_path = f"{benchmark_path}/unstable_ext"
    stable_core_path = f"{benchmark_path}/stable_core"
    stable_ext_path = f"{benchmark_path}/stable_ext"

    os.system(f"mkdir -p {unstable_core_path}")
    os.system(f"mkdir -p {unstable_ext_path}")
    os.system(f"mkdir -p {stable_core_path}")
    os.system(f"mkdir -p {stable_ext_path}")
        
    ana = Analyzer("z_test")
    ana.timeout = 6e4 # 1 min
    # ana.res_stable = 80

    for proj in projs:
        print(proj.get_project_name())
        unss = []
        summaries = load_exp_sums(proj, solvers=[proj.orig_solver, Z3_4_12_1])
        for solver in [proj.orig_solver, Z3_4_12_1]:
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
    c = Analyzer("z_test")
    c.timeout = 6e4
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
        clean_dir = proj.clean_root_dir
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

def _plot_srs(cfg, rows, sp):
    dps = np.zeros((len(rows), 3))
    for query_row in rows:
        group_blobs = query_row[2]

        for k in range(len(group_blobs)):
            success = count_within_timeout(group_blobs[k], RCode.UNSAT, timeout=6e4)
            dps[rows.index(query_row), k] = percentage(success, 61)
    end = 0
    mutations = [str(p) for p in cfg.enabled_muts]
    
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

    for proj in tqdm(ALL_PROJS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_sums(proj, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
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
#     c = Analyzer("z_test")
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
#     # th.unsolvable = 20
#     # th.res_stable = 80

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