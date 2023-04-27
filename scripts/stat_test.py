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
    # power = zt_ind_solve_power(effect_size=effect_size, nobs1=sample_size, alpha=significance, power=None, ratio=0.0, alternative=alternative)
    # print(power)

    # report
    # print("z_stat: %0.3f, p_value: %0.3f" % (stat, p_value))
    print(f'{stat=:.4} {p_value=:.4}')

    if p_value > significance:
        print(
            f"Fail to reject the null hypothesis - we have nothing else to say; samples do NOT support true proportion <=> {null_hypothesis}"
        )
    else:
        print(
            f"Reject the null hypothesis - suggest the alternative hypothesis is true; samples support true proportion {direction} {null_hypothesis}"
        )

def chi2_test():
    # std = np.std(ts)
    # print(std)
    std = int(argv[1])
    size = 2
    est = int(argv[2])
    T = (size - 1) * ((std / est) ** 2)
    print(T)
    # c1 = scipy.stats.chi2.ppf(0.05, df=size-1)
    c2 = scipy.stats.chi2.ppf(1-0.05, df=size-1)
    print(c2)
    print(T > c2)
    # print(T < c1)

z_test()
