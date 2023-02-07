import matplotlib.pyplot as plt
import numpy as np
from matplotlib.pyplot import figure
from matplotlib import ticker
from scipy.stats import gaussian_kde
import statistics
import seaborn as sns

def plot_cdf(sp, data, label):
    n = len(data)
    y = np.arange(n) / float(n)
    label = label
    sp.plot(np.sort(data), y, marker=",", label=label)

def plot_csum(sp, data, label):
    n = len(data)
    y = np.arange(n)
    sp.plot(np.sort(data), y, marker=",", label=label)

def plot_rev_csum(sp, data, label):
    n = len(data)
    y = np.arange(n)[::-1] / float(n)
    sp.plot(np.sort(data), y, marker=",", label=label)

def setup_project_time_cdfs(pname):
    figure, axis = plt.subplots(3, 1)
    figure.suptitle(pname, fontsize=16)

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
    sp.set_title(f'{sname}')

    for label, dist in dists.items():
        plot_rev_csum(sp, dist, label)
    sp.set_ylabel("cumulative count above threshold")
    sp.set_xlabel("response time variance threshold")
    sp.set_xscale("log")
    sp.set_xlim(left=0.5e-2)
    sp.set_yscale("log")
    sp.legend()

def plot_success_rate_cdfs(sp, dists, sname):
    sp.set_title(f'{sname}')

    for label, dist in dists.items():
        dist = list(filter(lambda x: x >= 0.005, dist))
        plot_cdf(sp, dist, label)
    sp.set_ylabel("cumulative count below threshold")
    sp.set_xlabel("success rate threshold")
    sp.set_xlim(left=0.5e-2)
    # sp.set_xlim(right=1-0.5e-2)
    # sp.set_xscale("log")
    sp.set_yscale("log")
    sp.legend()
