from analysis_utils import *
import matplotlib.font_manager as font_manager
import matplotlib

FONT = {'family': 'Raleway', 'size': 20}
matplotlib.rc('font', **FONT)

def plot_presentation_latest():
    projs = MAIN_PROJS
    project_names = [proj.name for proj in projs]

    if cache_exists("overall_data"):
        data = cache_load("overall_data")
    else:
        data = mp_categorize_projects(projs, MAIN_Z3_SOLVERS)
        data = np.array(data)
        cache_save(data, "overall_data")

    solver_names = [SOLVER_LABELS[s] for s in MAIN_Z3_SOLVERS]

    bar_width = len(project_names)/20
    br = 0

    for index in range(0, 4):
        fig, ax = plt.subplots()
        fig.set_size_inches(12, 8)

        pi = 0
        project_row = data[pi]
        pcs = np.zeros((len(Stability), len(solver_names)))
        for i, ps in enumerate(project_row):
            pcs[:, i] = ps
        pcolor = PROJECT_COLORS[project_names[pi]]
        pcs = np.cumsum(pcs,axis=0)
        # print(project_row)
        
        usolv = pcs[1][-1]
        unstb = (pcs[2]-pcs[1])[-1]
        incon = (pcs[3]-pcs[2])[-1]
        
        # br = [x + bar_width for x in br]
        pcolor = PROJECT_COLORS[project_names[pi]]
        if index >= 1:
            plt.bar(br, usolv, width=bar_width, color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.8)
        if index >= 2:
            plt.bar(br, height=unstb, bottom=usolv, width=bar_width, color=pcolor, edgecolor='black', linewidth=0.8)
        if index >= 3:
            plt.bar(br, height=incon, bottom=unstb+usolv, width=bar_width, color="w", edgecolor='black', linewidth=0.8)

        plt.ylim(bottom=0, top=9)
        plt.xlim(left=-0.25, right=5.25)
        plt.xticks([r for r in range(len(project_names))], 
                [PROJECT_LABELS[p] for p in project_names], rotation=30, ha='center')
        # ax.tick_params(axis='both', which='major', prop=FONT)
        # ax.tick_params(axis='both', which='minor', prop=FONT)
        plt.tight_layout()
        plt.savefig(f"fig/overall_latest/init{index}.png", dpi=300)
        plt.close()

    for index in range(0, len(project_names)):
        fig, ax = plt.subplots()
        fig.set_size_inches(12, 8)
        br = -1

        for pi, project_row in enumerate(data):
            br += 1
            if pi > index:
                continue
            pcs = np.zeros((len(Stability), len(solver_names)))
            for i, ps in enumerate(project_row):
                pcs[:, i] = ps
            pcolor = PROJECT_COLORS[project_names[pi]]
            pcs = np.cumsum(pcs,axis=0)
            # print(project_row)
            
            usolv = pcs[1][-1]
            unstb = (pcs[2]-pcs[1])[-1]
            incon = (pcs[3]-pcs[2])[-1]
            
            # br = [x + bar_width for x in br]
            pcolor = PROJECT_COLORS[project_names[pi]]
            plt.bar(br, usolv, width=bar_width,
                    color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.8)
            plt.bar(br, height=unstb, bottom=usolv, width=bar_width,
                    color=pcolor, edgecolor='black', linewidth=0.8)
            plt.bar(br, height=incon, bottom=unstb+usolv, width=bar_width,
                    color="w", edgecolor='black', linewidth=0.8)
            # print(usolv)
            # break

        plt.ylim(bottom=0, top=9)
        plt.xlim(left=-0.25, right=5.25)
        plt.xticks([r for r in range(len(project_names))], 
                [PROJECT_LABELS[p] for p in project_names], rotation=30, ha='center', fontsize=FSIZE,  fontname=FNAME)
        ax.tick_params(axis='both', which='major', labelsize=FSIZE)
        ax.tick_params(axis='both', which='minor', labelsize=FSIZE)
        plt.tight_layout()
        plt.savefig(f"fig/overall_latest/{index}.png", dpi=300)
        plt.close()

def plot_presentation_overall():
    projs = MAIN_PROJS
    project_names = [proj.name for proj in projs]
    solver_names = [SOLVER_LABELS[s] for s in MAIN_Z3_SOLVERS]
    solver_labels = [f"{SOLVER_LABELS[s]}\n{s.date[:-3]}" for s in MAIN_Z3_SOLVERS]

    if cache_exists("overall_data"):
        data = cache_load("overall_data")
    else:
        data = mp_categorize_projects(projs, MAIN_Z3_SOLVERS)
        data = np.array(data)
        cache_save(data, "overall_data")

    bar_width = len(solver_names)/70

    fig, ax = plt.subplots()
    fig.set_size_inches(16, 8)

    br = np.arange(len(solver_names))
    br = [x - 2 * bar_width for x in br]
    handles = []


    for pi, project_row in enumerate(data):
        br = [x + bar_width for x in br]
        if pi > 0:
            continue

        pcs = np.zeros((len(Stability), len(solver_names)))

        pcs[:, 7] = project_row[7]
        pcolor = PROJECT_COLORS[project_names[pi]]
        pcs = np.cumsum(pcs,axis=0)

        plt.bar(br, height=pcs[1], width=bar_width,
                color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.8)
        hd = plt.bar(br, height=pcs[2]-pcs[1], bottom=pcs[1], width=bar_width,
                color=pcolor, edgecolor='black', linewidth=0.8)
        handles.append(hd)
        plt.bar(br, height=pcs[3]-pcs[2], bottom=pcs[2], width=bar_width,
                color="w", edgecolor='black', linewidth=0.8)

    plt.xticks([r + 2 * bar_width for r in range(len(solver_names))], solver_labels, rotation=30, ha='right', fontsize=FSIZE)
    from matplotlib.lines import Line2D
    # woot = Line2D([0], [0], marker="*", color='black', linestyle='None', label='artifact solver'),
    plt.legend(handles,  [PROJECT_LABELS[p] for p in project_names[:1]], loc='upper left', fontsize=FSIZE)
    # plt.ylabel(r'query proportion ($\%$)', fontsize=FSIZE, fontname=FNAME)
    # plt.xlabel('solver versions and release dates', fontsize=FSIZE, fontname=FNAME)
    plt.ylim(bottom=0, top=9)
    plt.xlim(left=-0.25, right=7.65)

    plt.tight_layout()
    plt.savefig(f"fig/overall/00.png", dpi=300)
    plt.close()
    
    keep_sets = [{0}, {0, 1}, {0, 1, 2}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 1, 2, 3, 4, 5}, {0, 2, 3, 4, 5}, {2, 3}]
    
    for keep_set in keep_sets:
        fig, ax = plt.subplots()
        fig.set_size_inches(16, 8)

        br = np.arange(len(solver_names))
        br = [x - 2 * bar_width for x in br]

        # data[project_index][solver_index][category_index]
        handles = []

        for pi, project_row in enumerate(data):
            br = [x + bar_width for x in br]

            if pi not in keep_set:
                continue

            pcs = np.zeros((len(Stability), len(solver_names)))

            for i, ps in enumerate(project_row):
                pcs[:, i] = ps
            pcolor = PROJECT_COLORS[project_names[pi]]
            pcs = np.cumsum(pcs,axis=0)

            plt.bar(br, height=pcs[1], width=bar_width,
                    color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.8)
            hd = plt.bar(br, height=pcs[2]-pcs[1], bottom=pcs[1], width=bar_width,
                    color=pcolor, edgecolor='black', linewidth=0.8)
            handles.append(hd)
            plt.bar(br, height=pcs[3]-pcs[2], bottom=pcs[2], width=bar_width,
                    color="w", edgecolor='black', linewidth=0.8)

            for i in range(len(solver_names)):
                if solver_names[i] == projs[pi].artifact_solver.pretty_name():
                    plt.scatter(br[i], pcs[3][i] + 0.2, marker="*", color='black',  linewidth=0.8, s=40)

        # label_x = 2.85
        # leable_y = 5
        # ls = (0, (1, 5))

        # if 0 in keep_set:
        #     plt.text(label_x, leable_y, r'unsolvable', horizontalalignment='right', fontsize=FSIZE, fontname=FNAME)
        #     plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 1.0], 
        #             'o', ls=ls, color='black', linewidth=2, ms=1)
        #     leable_y += 0.8
        #     plt.text(label_x, leable_y, r'unstable', horizontalalignment='right', fontsize=FSIZE, fontname=FNAME)
        #     plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 2.7],
        #             'o', ls=ls, color='black', linewidth=2, ms=1)
        #     leable_y += 0.8
        #     plt.text(label_x, leable_y, r'inconclusive', horizontalalignment='right', fontsize=FSIZE, fontname=FNAME)
        #     plt.plot([label_x + 0.05, 3.88], [leable_y + 0.05, 4.7],
        #             'o', ls=ls, color='black', linewidth=2, ms=1)

        plt.xticks([r + 2 * bar_width for r in range(len(solver_names))], solver_labels, rotation=30, ha='right', fontsize=FSIZE, fontname=FNAME)
        from matplotlib.lines import Line2D
        woot = Line2D([0], [0], marker="*", color='black', linestyle='None', label='artifact solver'),
        plt.legend(handles + [woot],  [PROJECT_LABELS[project_names[p]] for p in keep_set] + ['artifact solver'], loc='upper left', fontsize=FSIZE)

        plt.ylim(bottom=0, top=9)
        plt.xlim(left=-0.25, right=7.65)
        ax.tick_params(axis='both', which='major', labelsize=FSIZE)
        ax.tick_params(axis='both', which='minor', labelsize=FSIZE)
        
        plt.tight_layout()
        keep_set = "_".join([str(k) for k in sorted(keep_set)])
        plt.savefig(f"fig/overall/{keep_set}.png", dpi=300)
        plt.close()

def plot_presentation_ext_cutoff():
    max_time = 150
    cutoffs = [i for i in range(10, max_time+1, 1)]
    proj = D_LVBKV
    solver = Z3_4_12_1
    rows = load_exp_sums(proj, True)[solver]
    steps = [10, 30, 60]

    for index in range(0, len(steps)+1):
        fig, ax = plt.subplots()
        fig.set_size_inches(12, 8)
        sp = plt
        # name = proj.name
        diffs, unstables, unsolvables = get_data_time_cutoff(proj.name, rows, cutoffs, steps)
        sp.plot(cutoffs, unsolvables,
                label=r"unsolvable",color=MUTATION_COLORS["unsolvable"], linewidth=1.5)
        sp.plot(cutoffs, unstables,
                label=r"unstable" + "(+0s)", color=MUTATION_COLORS["unstable"], linewidth=1.5)
            
        step_colors = ["#A6BDD7", "#817066", "#F6768E"]
        for j, step in enumerate(steps):
            if j >= index:
                continue
            changes = diffs[j]
            sp.plot(cutoffs[:len(changes)], changes,
                    label= r"unstable" + f"(+{step}s)",  linestyle='--', color=step_colors[j], linewidth=1.5)
            sp.vlines(cutoffs[-1]-step,
                    ymin=0, ymax=changes[-1], linestyle='--', color=step_colors[j], linewidth=1.5)

        sp.xlim(left=min(cutoffs), right=max_time)
        sp.ylim(bottom=0)
        
        sp.legend(prop={'size':FSIZE})
        # sp.ylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
        # sp.xlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME) 
        # sp.title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
        sp.xticks([10, 30, 60, 90, 120, 150])    
        plt.tight_layout()

        ax.tick_params(axis='both', which='major', labelsize=FSIZE)
        ax.tick_params(axis='both', which='minor', labelsize=FSIZE)
        # create dir if not exist
        os.system(f"mkdir -p fig/time_cutoff/{proj.name}")
        plt.savefig(f"fig/time_cutoff/{proj.name}/time_ext.{index}.png", dpi=300)
        plt.close()

def plot_presentation_pert_diff():
    for proj in [D_KOMODO, D_FVBKV]:
        solver = Z3_4_12_1
        
        mutations = [str(p) for p in MAIN_EXP.enabled_muts]
        cutoffs = np.arange(10, 61, 0.5)

        top = 0
        summaries = load_exp_sums(proj, True)
        rows = summaries[solver]

        name = proj.name
        if cache_exists(f"pert_diff_{name}"):
            categories = cache_load(f"pert_diff_{name}")
        else:
            categories = mp_get_all_cutoff_categories(rows, cutoffs, mutations)
            cache_save(categories, f"pert_diff_{name}")

        keys = ["unstable"] + mutations + ["unsolvable", "intersect"]
        points = {p:[] for p in keys}

        for j in cutoffs:
            for k, v in categories[j].items():
                points[k].append(percentage(len(v), len(rows)))

        for i, combos in enumerate([["unstable"], ["unstable", "shuffle"], ["unstable", "shuffle", "rename"], ["unstable", "shuffle", "rename", "reseed"], ["unstable", "reseed", "rename", "shuffle", "intersect"]]):
            fig, ax = plt.subplots()
            sp = plt
            fig.set_size_inches(8, 8)
            
            for k in points:
                if k not in combos or k == "unsolvable":
                    continue
                l = MUTATION_LABELS[k] if k in MUTATION_LABELS else k
                if k == "unstable":
                    l = r"unstable" + "(all methods)"
                sp.plot(cutoffs, points[k], label=l, color=MUTATION_COLORS[k], linewidth=1.5)
                top = max(top, max(points[k]))

            sp.xlim(left=min(cutoffs), right=60)

            if proj == D_KOMODO:
                top = 6
            else:
                top = 4
            sp.ylim(bottom=0, top=top)
            sp.yticks([i for i in range(top)])
            sp.xticks([10, 20, 30, 40, 50, 60])
            ax.legend(loc='upper right', prop={'size':FSIZE})

            ax.tick_params(axis='both', which='major', labelsize=FSIZE)
            ax.tick_params(axis='both', which='minor', labelsize=FSIZE)
            # sp.title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
            # sp.ylabel(r"proportion of queries ($\%$)", fontsize=FSIZE, fontname=FNAME)
            # sp.xlabel("time limit (seconds)", fontsize=FSIZE, fontname=FNAME) 
            plt.tight_layout()

            os.system(f"mkdir -p fig/pert_diff/{proj.name}")
            plt.savefig(f"fig/pert_diff/{proj.name}/{i}.png", dpi=300)
            plt.close()

def plot_presentation_time_std():
    for proj in [D_KOMODO, FS_DICE]:
        solver = Z3_4_12_1

        mutations = [str(p) for p in MAIN_EXP.enabled_muts]

        y_bound = 0
        x_bound = 0

        if cache_exists(f"time_std_{proj.name}"):
            dps = cache_load(f"time_std_{proj.name}")
        else:    
            summaries = load_exp_sums(proj, True)
            rows = summaries[solver]
            dps = get_data_time_std(rows)
            cache_save(dps, f"time_std_{proj.name}")

        for i in range(len(mutations)):
            xs, ys = get_cdf_pts(dps[i])
            ys = np.flip(ys)
            try:
                start = np.where(xs > 1)[0][0]
            except:
                start = -1
            y_bound = max(ys[start-1], y_bound)
            x_bound = max(np.max(xs), x_bound)
            
        for index in range(len(mutations)):
            fig, ax = plt.subplots()
            sp = plt
            fig.set_size_inches(8, 8)

            for i in range(index+1):
                xs, ys = get_cdf_pts(dps[i])
                ys = np.flip(ys)
                label = MUTATION_LABELS[mutations[i]]
                color = MUTATION_COLORS[mutations[i]]
                sp.plot(xs, ys, label=label, color=color)
                sp.xlim(left=1)
                ticks = [1, 5, 10, 15, 20]
                sp.xticks(ticks)
                sp.ylim(bottom=0, top=y_bound)

            ax.tick_params(axis='both', which='major', labelsize=FSIZE)
            ax.tick_params(axis='both', which='minor', labelsize=FSIZE)
            sp.legend(loc='upper right', prop={'size':FSIZE})
            # sp.title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)
            # fig.supylabel(r"proportion of queries exceding ($\%$)", fontsize=FSIZE, fontname=FNAME)
            # fig.supxlabel("time standard deviation (seconds)", fontsize=FSIZE, fontname=FNAME)
            plt.tight_layout()

            os.system(f"mkdir -p fig/time_stable/{proj.name}")
            plt.savefig(f"fig/time_stable/{proj.name}/{index}.png", dpi=300)
            plt.close()

def plot_presentation_time_scatter():
    proj = FS_VWASM
    solver = Z3_4_12_1
    
    if cache_exists(f"time_scatter_{proj.name}"):
        cats, scatters = cache_load(f"time_scatter_{proj.name}")
    else:
        summaries = load_exp_sums(proj, True)
        rows = summaries[solver]
        cats, scatters = _get_data_time_scatter(rows)
        cache_save((cats, scatters), f"time_scatter_{proj.name}")
    # others = list(set(range(len(rows))) - set(cats[Stability.STABLE]) - set(cats[Stability.UNSTABLE]))
    
    stables = cats[Stability.STABLE]
    unstables = cats[Stability.UNSTABLE]
    unsolvables = cats[Stability.UNSOLVABLE] + cats[Stability.UNKNOWN]
    inconclusives = cats[Stability.INCONCLUSIVE]
    # order = [2,1,0,3,4]
    order = ["region", "unsolvable", "unstable", "inconclusive", "stable"]

    for index in range(len(order)):
        figure, axis = plt.subplots()
        figure.set_size_inches(8, 8)
        sp = plt

        if "region" in order[:index+1]:
            sp.fill_between([0.01, 1000],  [0.01 * 1.5, 1000 * 1.5], [0.01, 1000], alpha=0.1, color="green", label=r"$\frac{x}{1.5} < y < 1.5x$")
            sp.fill_between([0.01, 1000],  [0.01, 1000], [0.01 / 1.5, 1000 / 1.5], alpha=0.1, color="green")

        if "unsolvable" in order[:index+1]:
            sp.scatter(scatters[:,0][unsolvables], scatters[:,1][unsolvables], s=8, color="r", marker="s", label=r"unsolvable")

        if "inconclusive" in order[:index+1]:    
            sp.scatter(scatters[:,0][inconclusives], scatters[:,1][inconclusives], s=8, label=r"inconclusive")

        if "unstable" in order[:index+1]:
            sp.scatter(scatters[:,0][unstables], scatters[:,1][unstables], s=8, color="orange", label=r"unstable")

        if "stable" in order[:index+1]:
            sp.scatter(scatters[:,0][stables], scatters[:,1][stables], s=8, color="#78A1BB", label=r"stable")

        # sp.scatter(scatters[:,0][[cats[Stability.Unk]], scatters[:,1][others], s=8, label="others")
        # print(pf, cfs, ps, css)
        # print(percentage(bounded, len(scatters)), mworse, len(scatters))
        # print(weightstats.ttost_paired(np.array(ys), np.array(xs), -0.57, -0.03))
        # print(weightstats.ttost_paired(np.array(ys), np.array(xs), 1.002, 1.015, transform=np.log))

        # sp.loglog([0.01, 1000], [0.01, 1000], color="black", linestyle="--",linewidth=0.75)
        sp.xlim(left=.1, right=160)
        sp.ylim(bottom=.1, top=160)
        sp.xscale("log")
        sp.yscale("log")
        handles, labels = axis.get_legend_handles_labels()
        # plt.title(make_title(proj, solver), fontsize=FSIZE, fontname=FNAME)

        sp.legend(loc="upper left", prop={'size':FSIZE})
        axis.set_aspect('equal', adjustable='box')
        axis.tick_params(axis='both', which='major', labelsize=FSIZE)
        axis.tick_params(axis='both', which='minor', labelsize=FSIZE)
        # figure.supxlabel("original time (seconds) log scale", fontsize=FSIZE, fontname=FNAME)
        # figure.supylabel("median mutant time (seconds) log scale", fontsize=FSIZE, fontname=FNAME)
        plt.tight_layout()

        os.system(f"mkdir -p fig/time_scatter/{proj.name}")
        plt.savefig(f"fig/time_scatter/{proj.name}/{index}.png", dpi=300)
        plt.close()

if __name__ == "__main__":
    # plot_presentation_latest()
    plot_presentation_overall()
    # plot_presentation_pert_diff()
    # plot_presentation_time_std()
    # plot_presentation_ext_cutoff()
    # plot_presentation_time_scatter()