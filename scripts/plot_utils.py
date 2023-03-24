import matplotlib.pyplot as plt
import numpy as np
from matplotlib.pyplot import figure
from matplotlib import ticker
from scipy.stats import gaussian_kde
import statistics
# import seaborn as sns

def get_cdf_pts(data):
    n = len(data)
    y = np.arange(n) * 100 / float(n) 
    return np.sort(data), y

def plot_csum(sp, data, label):
    n = len(data)
    y = np.arange(n)
    sp.plot(np.sort(data), y, marker=",", label=label)

def setup_fig(rows, columns):
    figure, axis = plt.subplots(rows, columns)

    figure.set_figheight(10 * rows)
    figure.set_figwidth(7.5 * columns)

    return figure, axis

def save_fig(figure, title, file):
    figure.suptitle(title, fontsize=16)
    plt.savefig(file)

def plot_time_overall(sps, dists, dists2, sname, colors):
    sp = sps[0]
    sp.set_title(f'{sname} response time cdf')

    for label, dist in dists2.items():
        xs, ys = get_cdf_pts(dist)
        sp.plot(xs, ys, marker=",", label=label, color=colors[label])
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("response time (log)")
    sp.legend()

    sp = sps[1]
    sp.set_title(f'{sname} response time standard deviation cdf')
    for label, dist in dists.items():
        xs, ys = get_cdf_pts(dist)
        if xs[-1] >= 1:
            li = len(xs) - np.where(xs>=1)[0][0] - 1
        sp.plot(xs, ys[::-1], marker=",", label=label, color=colors[label])
    sp.set_ylabel("cumulative percentage (%) above threshold")
    sp.set_xlabel("response time standard deviation (seconds) threshold log scale")
    sp.set_xscale("log")
    sp.set_xlim(left=0.001)
    sp.set_yscale("log")
    sp.legend()

def plot_result_overall(sps, dists, sname, colors):
    sp = sps[0]
    sp.set_title(f'{sname} success rate cdf')
    for label, dist in dists.items():
        xs, ys = get_cdf_pts(dist)
        sp.plot(xs, ys, marker=",", label=label, color=colors[label])
    sp.set_ylabel("cumulative percentage (%) below threshold")
    sp.set_xlabel("success rate (%) threshold")
    # sp.set_xlim(left=0, right=100)
    sp.set_xticks([i for i in range(0, 110, 10)])
    # sp.set_ylim(bottom=0)
    sp.legend()

    sp = sps[1]
    sp.set_title(f'{sname} (zoomed in 1%<=SR<=99%)')
    min_p, max_p = 100, 0
    for label, dist in dists.items():
        xs, ys = get_cdf_pts(dist)
        li = np.where(xs>=1)[0][0]
        hi = len(xs) - np.where(xs[::-1]<=99)[0][0] - 1
        min_p = min(ys[li], min_p)
        if li < hi:
            max_p = max(ys[hi], max_p)
            sp.plot(xs, ys, marker=",", label=label, color=colors[label])
    sp.set_ylabel("cumulative percentage (%) below threshold")
    sp.set_xlabel("success rate (%) threshold")
    sp.set_xlim(left=1, right=99)
    sp.set_ylim(bottom=min_p-0.1, top=max_p+0.1)
    sp.set_xticks([1] + [i for i in range(10, 100, 10)] + [99])
    sp.legend()
