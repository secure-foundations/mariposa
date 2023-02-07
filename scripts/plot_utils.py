import matplotlib.pyplot as plt
import numpy as np
from matplotlib.pyplot import figure
from matplotlib import ticker
from scipy.stats import gaussian_kde
import statistics
import seaborn as sns

def get_cdf_pts(data):
    n = len(data)
    y = np.arange(n) * 100 / float(n) 
    return np.sort(data), y

def plot_csum(sp, data, label):
    n = len(data)
    y = np.arange(n)
    sp.plot(np.sort(data), y, marker=",", label=label)

def plot_rev_csum(sp, data, label):
    n = len(data)
    y = np.arange(n)[::-1] / float(n)
    sp.plot(np.sort(data), y, marker=",", label=label)

def setup_fig(title, rows, columns):
    figure, axis = plt.subplots(rows, columns)
    figure.suptitle(title, fontsize=16)

    figure.set_figheight(20)
    figure.set_figwidth(10)

    return axis

def plot_time_cdfs(sp, dists, sname):
    sp.set_title(f'{sname}')

    for label, dist in dists.items():
        plot_cdf(sp, dist, label)
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("response time (log)")
    sp.set_xscale("log")
    sp.legend()

def plot_time_variance_cdfs(sp, dists, sname):
    count = len(dists['sseed'])
    sp.set_title(f'{sname} plain count: {count}')

    for label, dist in dists.items():
        plot_rev_csum(sp, dist, label)
    sp.set_ylabel("cumulative percentage (%) above threshold")
    sp.set_xlabel("response time variance (seconds) threshold log scale")
    sp.set_xscale("log")
    # sp.set_xlim(left=0.5e-2)
    sp.set_yscale("log")
    sp.legend()

def plot_success_rate_cdfs(sps, dists, sname):
    sp = sps[0]
    count = len(dists['sseed'])
    sp.set_title(f'{sname} plain count: {count}')
    for label, dist in dists.items():
        xs, ys = get_cdf_pts(dist)
        sp.plot(xs, ys, marker=",", label=label)
    sp.set_ylabel("cumulative percentage (%) below threshold")
    sp.set_xlabel("success rate (%) threshold")
    sp.legend()

    sp = sps[1]
    sp.set_title(f'{sname} (zoomed in 1%<=SR<=99%)')
    min_p, max_p = 100, 0
    for label, dist in dists.items():
        xs, ys = get_cdf_pts(dist)
        li = np.where(xs>=1)[0][0]
        hi = len(xs) - np.where(xs[::-1]<=99)[0][0] - 1
        if li < hi:
            min_p = min(ys[li], min_p)
            max_p = max(ys[hi], max_p)
            sp.plot(xs, ys, marker=",", label=label)
    sp.set_ylabel("cumulative percentage (%) below threshold")
    sp.set_xlabel("success rate (%) threshold")
    sp.set_xlim(left=1, right=99)
    sp.set_ylim(bottom=min_p-0.1, top=max_p+0.1)
    sp.set_xticks([1] + [i for i in range(10, 100, 10)] + [99])
    sp.legend()
