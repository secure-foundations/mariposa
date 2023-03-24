import statsmodels
import statsmodels.stats.proportion as prop
#  sm.power  zt_ind_solve_power
from sys import argv
import numpy as np
import scipy

significance = 0.05

def z_test():
    sample_success = int(argv[1])
    sample_size = int(argv[2])

    null_hypothesis = float(argv[3])

    direction = argv[4]

    # check our sample against Ho for Ha > Ho
    # for Ha < Ho use alternative='smaller'
    # for Ha != Ho use alternative='two-sided'
    alternative = "smaller" if direction == "<" else "larger"
    stat, p_value = prop.proportions_ztest(
        count=sample_success,
        nobs=sample_size,
        value=null_hypothesis,
        alternative=alternative,
        prop_var=null_hypothesis,
    )

    effect_size = prop.proportion_effectsize(sample_success/sample_size, null_hypothesis, method='normal')
    from statsmodels.stats.power import zt_ind_solve_power
    # p = NormalIndPower()
    # power = p.power(effect_size, sample_size, alpha=significance, ratio=0, alternative=alternative)
    power = zt_ind_solve_power(effect_size=effect_size, nobs1=sample_size, alpha=significance, power=None, ratio=0.0, alternative=alternative)
    print(power)

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

def chi2_test():
    ts = [317, 364, 595, 369, 297, 368, 322, 314, 360, 797, 323, 394, 377, 465, 360, 943, 356, 306, 411, 326, 331, 427, 981, 456, 329, 9361, 757, 288, 402, 394, 859, 344, 375, 399, 368, 300, 377, 349, 310, 420, 361, 374, 326, 511, 360, 3390, 407, 942, 537, 698, 327, 704, 341, 1082, 27014, 336, 587, 304, 369, 454]
    std = np.std(ts)
    # print(std)
    size = len(ts)
    est = 1000
    T = (size - 1) * ((std / est) ** 2)
    print(T)
    # c1 = scipy.stats.chi2.ppf(0.05, df=size-1)
    c2 = scipy.stats.chi2.ppf(1-0.05, df=size-1)
    print(c2)
    print(T > c2)
    # print(T < c1)

chi2_test()
