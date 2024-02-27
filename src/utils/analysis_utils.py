import numpy as np

def is_ratio(x):
    return type(x) == float and 0 < x < 1

def percent(a, b):
    return a * 100 / b

def rd_percent(a, b):
    return round(a * 100 / b, 2)

def rd_percent_str(a, b):
    return f"{rd_percent(a, b)}%"

def get_sets_diff(a, b):
    return a - b, b - a, a & b

def print_sets_diff(a, b, name_a="a", name_b="b"):
    diff0, diff1, _ = get_sets_diff(a, b)
    if len(diff0) != 0:
        print(f"[INFO] items in {name_a} but not in {name_b}")
        for i in diff0:
            print("\t" + i)
        print(f"[INFO] {len(diff0)} in {name_a} but not in {name_b}")
    if len(diff1) != 0:
        print(f"[INFO] items in {name_b} but not in {name_a}")
        for i in diff1:
            print("\t" + i)
        print(f"[INFO] {len(diff1)} in {name_b} but not in {name_a}")

def get_cdf_pts(data):
    n = len(data)
    y = np.arange(n) * 100 / float(n) 
    return np.sort(data), np.insert(y[1:], n-1, 100)

def tex_fmt_percent(x, suffix=False):
    assert x >= -100 and x <= 100
    res = f"%.1f" % x
    if suffix: res += r"\%"
    assert x >= 0
    return res

def tex_double_column(x):
    return r"\multicolumn{2}{c}{" + x + r"}"
