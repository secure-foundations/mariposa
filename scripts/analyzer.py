from db_utils import *
from vbkv_filemap import *
import shutil

from configs.projects import *
from configs.experiments import *
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
    "D_KOMODO": "Komodo(D)",
    "D_FVBKV": "VeriBetrKV(D)",
    "D_LVBKV": "VeriBetrKV(L)",
    "FS_DICE": r"DICE$^{\star}$(F)",
    "FS_VWASM": "vWasm(F)",
    "S_KOMODO": "Komodo(S)",
} 

def make_title(cfg, solver):
    return f"{PROJECT_LABELS[cfg.qcfg.name]} {solver.pstr()}"

def get_color_map(keys):
    assert len(keys) <= len(COLORS)
    return {k: COLORS[i] for i, k in enumerate(keys)}

PROJECT_COLORS = get_color_map([c for c in PROJECT_LABELS])

MUTATION_COLORS = {
    "shuffle": "#803E75",        
    "rename": "#FF6800",
    "rseed": "#A6BDD7",
    "union": "#FFB300",
    "unstable": "#FFB300",
    "unsolvable": "#C10020",
    "intersect": "#817066",
}

MUTATION_LABELS = {
    "shuffle":r"shuffling",
    "rseed": r"reseeding",
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

def get_unknowns(cfg):
    th = Classifier("strict")
    th.timeout = 6e4
    summary = load_solver_summary_table(cfg, cfg.qcfg.project.orig_solver)
    assert summary is not None
    categories = th.categorize_queries(summary)
    return categories[Stability.UNKNOWN]

def load_exp_results(cfg, skip_unknowns=True, solvers=None):
    summaries = dict()

    if skip_unknowns:
        unknowns = get_unknowns(cfg)
    else:
        unknowns = set()
        
    if solvers is None:
        solvers = cfg.samples

    for solver in cfg.samples:
        nrows = load_solver_summary_table(cfg, solver, unknowns)
        if nrows is None:
            continue
        summaries[solver] = nrows
    return summaries

def _async_categorize_project(ratios, key, rows):
    classifier = Classifier("z_test")
    classifier.timeout = 6e4 # 1 min
    items = classifier.categorize_queries(rows)
    ps, _ = get_category_percentages(items)
    ratios[key] = ps

def _mp_categorize_projects(cfgs, solver_names):
    manager = mp.Manager()
    ratios = manager.dict()

    for cfg in cfgs:
        summaries = load_exp_results(cfg)
        pool = mp.Pool(processes=8)
        for solver in solver_names:
            key = (cfgs.index(cfg), solver_names.index(solver))
            rows = summaries[solver]
            pool.apply_async(_async_categorize_project, 
                            args=(ratios, key, rows,))
        pool.close()
        pool.join()

    category_count = len(Stability)
    data = np.zeros((len(cfgs), len(solver_names), category_count))

    for key in ratios:
        i, j = key
        data[i][j] = [ratios[key][s] for s in Stability]

    return data

def plot_paper_overall(cfgs=ALL_CFGS):
    project_names = [cfg.qcfg.name for cfg in cfgs]
    solver_names = [str(s) for s in Z3_SOLVERS_ALL]

    # data = _mp_categorize_projects(cfgs, solver_names)
    data = [[[0.0, 0.48685491723466406, 0.43816942551119764, 0.7789678675754625, 98.29600778967868], [0.0, 0.5842259006815969, 0.5842259006815969, 0.6329113924050633, 98.19863680623175], [0.0, 0.6329113924050633, 0.2921129503407984, 0.5842259006815969, 98.49074975657254], [0.0, 0.5355404089581305, 0.3894839337877313, 0.2921129503407984, 98.78286270691333], [0.0, 1.7526777020447906, 2.288218111002921, 1.2171372930866602, 94.74196689386562], [0.0, 2.5803310613437196, 4.625121713729309, 1.3631937682570594, 91.43135345666991], [0.0, 2.4342745861733204, 4.430379746835443, 1.2171372930866602, 91.91820837390458], [0.0, 2.5316455696202533, 5.0146056475170395, 1.071080817916261, 91.38266796494645]], [[0.0, 0.258732212160414, 0.6468305304010349, 0.0, 99.09443725743856], [0.0, 0.258732212160414, 0.6468305304010349, 0.0, 99.09443725743856], [0.0, 0.129366106080207, 0.6468305304010349, 0.0, 99.22380336351875], [0.0, 0.0, 0.38809831824062097, 0.0, 99.61190168175938], [0.0, 0.0, 0.129366106080207, 0.0, 99.87063389391979], [0.0, 0.258732212160414, 0.258732212160414, 0.0, 99.48253557567917], [0.0, 0.258732212160414, 0.258732212160414, 0.0, 99.48253557567917], [0.0, 0.129366106080207, 0.517464424320828, 0.0, 99.35316946959897]], [[0.0, 0.6011647567161376, 0.7138831486004134, 0.3569415743002067, 98.32801052038324], [0.0, 0.6011647567161376, 0.7702423445425511, 0.1690775878264137, 98.4595153109149], [0.0, 0.1690775878264137, 0.6199511553635169, 0.1690775878264137, 99.04189366898366], [0.0, 0.3381551756528274, 0.7138831486004134, 0.1502911891790344, 98.79767048656772], [0.0, 0.375727972947586, 2.536163817396205, 0.5072327634792411, 96.58087544617696], [0.0, 0.6763103513056548, 3.1373285741123427, 0.3381551756528274, 95.84820589892918], [0.0, 0.563591959421379, 3.118542175464963, 0.3381551756528274, 95.97971068946083], [0.0, 0.563591959421379, 2.911891790343791, 0.3381551756528274, 96.18636107458201]], [[0.0, 0.5755395683453237, 0.28776978417266186, 0.1618705035971223, 98.9748201438849], [0.0, 0.5575539568345323, 0.3237410071942446, 0.12589928057553956, 98.99280575539568], [0.0, 0.3597122302158273, 0.8812949640287769, 0.0539568345323741, 98.70503597122303], [0.0, 0.3057553956834532, 0.4856115107913669, 0.0539568345323741, 99.15467625899281], [0.0, 0.4136690647482014, 2.949640287769784, 0.1079136690647482, 96.52877697841727], [0.0, 0.5575539568345323, 3.2014388489208634, 0.17985611510791366, 96.06115107913669], [0.0, 0.5215827338129496, 3.3633093525179856, 0.1618705035971223, 95.95323741007195], [0.0, 0.539568345323741, 3.147482014388489, 0.1618705035971223, 96.15107913669065]], [[0.0, 1.3201320132013201, 0.33003300330033003, 0.132013201320132, 98.21782178217822], [0.0, 1.2541254125412542, 0.33003300330033003, 0.132013201320132, 98.28382838283828], [0.0, 1.1221122112211221, 0.39603960396039606, 0.132013201320132, 98.34983498349835], [0.0, 0.594059405940594, 0.528052805280528, 0.132013201320132, 98.74587458745874], [0.0, 0.9240924092409241, 0.528052805280528, 0.264026402640264, 98.28382838283828], [0.0, 1.386138613861386, 0.6600660066006601, 0.0, 97.95379537953795], [0.0, 1.056105610561056, 0.594059405940594, 0.264026402640264, 98.08580858085809], [0.0, 0.9240924092409241, 0.7920792079207921, 0.132013201320132, 98.15181518151815]], [[0.0, 0.3462204270051933, 0.17311021350259664, 0.0, 99.48066935949221], [0.0, 0.3462204270051933, 0.17311021350259664, 0.0, 99.48066935949221], [0.0, 0.05770340450086555, 0.1154068090017311, 0.0, 99.8268897864974], [0.0, 0.0, 0.05770340450086555, 0.0, 99.94229659549913], [0.0, 0.17311021350259664, 0.4039238315060589, 0.0, 99.42296595499134], [0.0, 0.1154068090017311, 0.3462204270051933, 0.0, 99.53837276399308], [0.0, 0.0, 0.28851702250432776, 0.0, 99.71148297749568], [0.0, 0.05770340450086555, 0.2308136180034622, 0.0, 99.71148297749568]]]
    data = np.array(data)
    print(data.tolist())

    bar_width = len(solver_names)/70
    fig, ax = plt.subplots()
    fig.set_size_inches(7, 4.5)

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
            if solver_names[i] == str(cfgs[pi].qcfg.project.orig_solver):
                plt.scatter(br[i], pcs[3][i] + 0.2, marker="*", color='black',  linewidth=0.8, s=10)
            # if i == 4 and pi == 0:
            #     plt.bar(br[i], height=20, bottom=pcs[3][i], width=bar_width, 
            #             color='white', edgecolor='black', linewidth=0.3, linestyle=(0, (1, 5)))

    label_x = 2.85
    leable_y = 5
    ls = (0, (1, 5))
    
    plt.text(label_x, leable_y, r'\texttt{unsolvable}', horizontalalignment='right')
    plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 1.0], 
             'o', ls=ls, color='black', linewidth=0.5, ms=1)
    leable_y += 0.8
    plt.text(label_x, leable_y, r'\texttt{unstable}', horizontalalignment='right')
    plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 2.7],
             'o', ls=ls, color='black', linewidth=0.5, ms=1)
    leable_y += 0.8
    plt.text(label_x, leable_y, r'\texttt{inconclusive}', horizontalalignment='right')
    plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 4.7],
             'o', ls=ls, color='black', linewidth=0.5, ms=1)
    # plt.text(3.5, 5.45, r'\texttt{stable}' + "\n" + r"stack up to 100\%" + "\n" + "(unplotted)", horizontalalignment='right')
    # plt.plot([3.55, 3.88], [6.40, 6.75], 'o', ls='-', color='black', linewidth=0.2, ms=2)

    solver_lables = [f"{s.pstr()}\n{s.data[:-3]}" for s in Z3_SOLVERS_ALL]
    ax.tick_params(axis='both', which='major')
    plt.xticks([r + 2 * bar_width for r in range(len(solver_names))], solver_lables, rotation=30, ha='right')
    from matplotlib.lines import Line2D
    woot = Line2D([0], [0], marker="*", color='black', linestyle='None', label='artifact solver'),
    plt.legend(handles + [woot],  [PROJECT_LABELS[p] for p in project_names] + ['artifact solver'])
    plt.ylabel(r'query proportion ($\%$)', fontsize=FSIZE, fontname=FNAME)
    plt.xlabel('solver versions and release dates', fontsize=FSIZE, fontname=FNAME)
    plt.ylim(bottom=0, top=9)
    plt.tight_layout()
    plt.savefig("fig/all_paper.pdf")
    plt.close()

def _get_data_time_scatter(rows):
    pf, cfs = 0, 0
    ps, css = 0, 0

    classifier = Classifier("z_test")
    cats = {i: [] for i in Stability }

    scatters = np.zeros((len(rows), 2))
    for i, query_row in enumerate(rows):
        group_blobs = query_row[2]

        plain_res = group_blobs[0][0][0]
        plain_time = group_blobs[0][1][0]
        mutants = np.hstack((group_blobs[0,:,1:], group_blobs[1,:,1:], group_blobs[2,:,1:]))

        cat = classifier.categorize_query(group_blobs)[0]
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
    for i, cfg in enumerate([D_KOMODO_CFG, FS_VWASM_CFG]):
        rows = load_exp_results(cfg, True, [solver])[solver]
        axis[i].set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
        _plot_time_scatter(rows, axis[i])
    figure.supxlabel("original time (seconds)", fontsize=FSIZE, fontname=FNAME)
    figure.supylabel("median mutant time (seconds)", fontsize=FSIZE, fontname=FNAME)
    plt.tight_layout()
    plt.savefig(f"fig/time_scatter/scatter_paper.pdf")
    plt.close()

def plot_appendix_time_scatter():
    rc, cc = 2, 4
    for cfg in tqdm(ALL_CFGS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)

        summaries = load_exp_results(cfg, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_time_scatter(rows, sp)
            sp.set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("original time (seconds)", fontsize=FSIZE, fontname=FNAME)
        figure.supylabel("median mutant time (seconds)", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()
        plt.savefig(f"fig/time_scatter/{cfg.qcfg.name}.pdf")
        plt.close()

def _get_data_time_std(rows):
    classifier = Classifier("z_test")
    classifier.timeout = 6e4 # 1 min

    items = classifier.categorize_queries(rows)
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

def _plot_time_std(rows, sp):
    x_bound = 0
    y_bound = 0
    dps = _get_data_time_std(rows)
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]

    for i in range(len(perturbs)):
        xs, ys = get_cdf_pts(dps[i])
        ys = np.flip(ys)
        try:
            start = np.where(xs > 1)[0][0]
        except:
            start = 0
        y_bound = max(ys[start], y_bound)
        x_bound = max(x_bound, max(xs))
        label = MUTATION_LABELS[perturbs[i]]
        color = MUTATION_COLORS[perturbs[i]]
        sp.plot(xs, ys, label=label, color=color)
    sp.set_xlim(left=1)
    sp.set_ylim(bottom=0, top=y_bound)

def plot_appendix_time_std():
    rc, cc = 2, 4

    for cfg in tqdm(ALL_CFGS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_results(cfg, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_time_std(rows, sp)
            sp.set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
            sp.legend()
        figure.supylabel(r"proportion of queries" "\n" r"above threshold ($\%$)", fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("time standard deviation (seconds)", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()
        plt.savefig(f"fig/time_stable/{cfg.qcfg.name}.pdf")
        plt.close()    

def plot_paper_time_std():
    figure, axis = plt.subplots(1, 2)
    figure.set_size_inches(7, 4)
    solver = Z3_4_12_1
    for i, cfg in enumerate([D_KOMODO_CFG, FS_VWASM_CFG]):
        rows = load_exp_results(cfg, True, [solver])[solver]
        axis[i].set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
        _plot_time_std(rows, axis[i])
    axis[0].legend()
    figure.supylabel(r"proportion of queries" "\n" r"above threshold ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time standard deviation (seconds)", fontsize=FSIZE, fontname=FNAME)
    plt.tight_layout()
    plt.savefig(f"fig/time_stable/std_paper.pdf")
    plt.close()

def _async_cutoff_categories(categories, i, rows, perturbs):
    classifier = Classifier("z_test")
    classifier.timeout = i * 1e3
    cur = {p: set() for p in perturbs + ["unsolvable", "unstable", "intersect"]}

    for query_row in rows:
        plain_path = query_row[0]
        group_blobs = query_row[2]
        cat, votes = classifier.categorize_query(group_blobs)
        if cat == Stability.UNSTABLE:
            cur["unstable"].add(plain_path)
        elif cat == Stability.UNSOLVABLE:
            cur["unsolvable"].add(plain_path)
        for k, p in enumerate(perturbs):
            if votes[k] == Stability.UNSTABLE:
                cur[p].add(plain_path)
        if set(votes.values()) == {Stability.UNSTABLE}:
            # if all of the perturbations is unstable
            cur["intersect"].add(plain_path)

    assert(len(cur["intersect"]) <= len(cur["rseed"]))
    categories[i] = cur

def _mp_get_all_cutoff_categories(rows, cutoffs, perturbs):
    manager = mp.Manager()
    pool = mp.Pool(processes=8)
    categories = manager.dict()

    for i in cutoffs:
        # print(i)
        # _async_cutoff_categories(categories, i, rows, perturbs)
        pool.apply_async(_async_cutoff_categories, 
                         args=(categories, i, rows, perturbs,))
    pool.close()
    pool.join()
    return categories

def _plot_pert_diff(rows, sp):
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
    cutoffs = np.arange(10, 61, 0.5)

    top = 0
    total = len(rows)

    categories = _mp_get_all_cutoff_categories(rows, cutoffs, perturbs)
    keys = ["unstable"] + perturbs + ["unsolvable", "intersect"]
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
    sp.set_xticks([15, 30, 45, 60])

def plot_appendix_pert_diff():
    rc, cc = 2, 4

    for cfg in tqdm(ALL_CFGS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_results(cfg, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_pert_diff(rows, sp)
            sp.legend()
            sp.set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
        figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()

        plt.savefig(f"fig/pert_diff/{cfg.qcfg.name}.pdf")
        plt.close()

def plot_paper_pert_diff():
    figure, axis = plt.subplots(1, 2)
    figure.set_size_inches(7, 4)
    cfg = D_KOMODO_CFG
    summaries = load_exp_results(cfg, True)
    for index, solver in enumerate([cfg.qcfg.project.orig_solver, Z3_4_12_1]):
        sp = axis[index]
        rows = summaries[solver]
        _plot_pert_diff(rows, sp)
        sp.set_ylim(top=6)
        sp.set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
    axis[0].legend()
    figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME)
    plt.tight_layout()
    plt.savefig(f"fig/pert_diff/pert_paper.pdf")
    plt.close()

# def _pert_cutoff(cfg, sp):
def _get_data_time_cutoff(rows, cutoffs, steps):
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]

    categories = _mp_get_all_cutoff_categories(rows, cutoffs, perturbs)
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

    # name = cfg.qcfg.name
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
    # sp.set_xticks([10, 30, 60, 90, 120, 150])

def plot_appendix_ext_cutoff():
    rc, cc = 2, 4

    for cfg in tqdm(ALL_CFGS):
        figure, axis = plt.subplots(rc, cc)
        figure.set_size_inches(15, 8)
        summaries = load_exp_results(cfg, True)
        for index, solver in enumerate(Z3_SOLVERS_ALL):
            sp = axis[int(index/cc)][int(index%cc)]
            rows = summaries[solver]
            _plot_ext_cutoff(rows, sp, 60)
            sp.set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
            sp.legend(loc='upper center', ncol=3)

        figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
        figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME) 
        
        plt.tight_layout()
        plt.savefig(f"fig/time_cutoff/{cfg.qcfg.name}.pdf")
        plt.close()    

def plot_paper_ext_cutoff():
    figure, axis = plt.subplots(2, 1)
    figure.set_size_inches(7, 6)
    solver = Z3_4_12_1
    for index, cfg in enumerate([D_KOMODO_CFG, D_FVBKV_CFG]):
        sp = axis[index]
        rows = load_exp_results(cfg, True)[solver]
        _plot_ext_cutoff(rows, sp, 150, [10, 30, 60])
        sp.set_title(make_title(cfg, solver), fontsize=FSIZE, fontname=FNAME)
        sp.set_ylim(bottom=0, top=8)
    
    axis[1].legend()
    figure.supylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
    figure.supxlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME) 
    plt.tight_layout()
    plt.savefig(f"fig/time_cutoff/cutoff_paper.pdf")
    plt.close()

