from statsmodels.stats.proportion import proportions_ztest
from sys import argv

significance = 0.05

def z_test():
    sample_success = int(argv[1])
    sample_size = int(argv[2])

    null_hypothesis = float(argv[3])

    direction = argv[4]

    # check our sample against Ho for Ha > Ho
    # for Ha < Ho use alternative='smaller'
    # for Ha != Ho use alternative='two-sided'
    stat, p_value = proportions_ztest(
        count=sample_success,
        nobs=sample_size,
        value=null_hypothesis,
        alternative="smaller" if direction == "<" else "larger",
        prop_var=null_hypothesis,
    )

    # report
    # print("z_stat: %0.3f, p_value: %0.3f" % (stat, p_value))
    print(f'{stat=:.3} {p_value=:.3}')

    if p_value > significance:
        print(
            f"Fail to reject the null hypothesis - we have nothing else to say; samples do NOT support true proportion <=> {null_hypothesis}"
        )
    else:
        print(
            f"Reject the null hypothesis - suggest the alternative hypothesis is true; samples support true proportion {direction} {null_hypothesis}"
        )

import numpy as np
import scipy

ts = [5982, 6653, 8364, 9198, 9233, 7163, 6050, 7724, 10607, 10841]
# std = np.std(ts)
std = 1001
# print(std)
size = 10
est = 1000
T = (size - 1) * ((std / est) ** 2)
print(T)
# c1 = scipy.stats.chi2.ppf(0.05, df=size-1)
c2 = scipy.stats.chi2.ppf(1-0.05, df=size-1)
print(c2)
print(T > c2)
# print(T < c1)
