import matplotlib.pyplot as plt

plt.rcParams['text.usetex'] = True
plt.rcParams["font.family"] = "cmr"

FSIZE = 100
# FNAME ='cmr'

COLORS = [
    "#803E75", # Strong Purple
    "#FF6800", # Vivid Orange
    "#A6BDD7", # Very Light Blue
    "#C10020", # Vivid Red
    "#FFB300", # Vivid Yellow
    "#817066", # Medium Gray
    "#F6768E", # Strong Purplish Pink
]

class GrourpPlotMeta:
    def __init__(self, gid, tex_name, color):
        self.name = gid
        self.tex_name = tex_name
        self.tex_cmd = "\\" + self.name.replace("_", "")
        self.color = color

GROUP_PLOT_META = {
    "d_komodo": GrourpPlotMeta("d_komodo", r"Komodo$_{D}$", COLORS[0]),
    "s_komodo": GrourpPlotMeta("s_komodo", r"Komodo$_S$", COLORS[1]),
    "d_fvbkv": GrourpPlotMeta("d_fvbkv", r"VeriBetrKV$_{D}$", COLORS[2]),
    "d_lvbkv": GrourpPlotMeta("d_lvbkv", r"VeriBetrKV$_{L}$", COLORS[3]),
    "fs_dice": GrourpPlotMeta("fs_dice", r"DICE$^\star_F$", COLORS[4]),
    "fs_vwasm": GrourpPlotMeta("fs_vwasm", r"vWasm$_F$", COLORS[5]),
}

def add_text(ax, x, y, text, left=True):
    if left:
        ax.text(x, y, text, ha="left", va="bottom")
    else:
        ax.text(x, y, text, ha="right", va="bottom")

def fmt_percent(x):
    return f"%.2f" % x + "\%"

def tex_fmt_percent(x, suffix=False):
    assert x >= -100 and x <= 100
    res = f"%.1f" % x
    if suffix: res += r"\%"
    assert x >= 0
    return res

def tex_fmt_int(x):
    assert x >= 0
    return f'{x:,}' 

def tex_double_column(x):
    return r"\multicolumn{2}{c}{" + x + r"}"