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

def save_project_time_cdfs(pname):
    name = f"fig/time_cdf_{pname}.png"
    plt.savefig(name)