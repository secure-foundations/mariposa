import matplotlib.pyplot as plt

plt.rcParams['text.usetex'] = True
plt.rcParams["font.family"] = "serif"

FSIZE = 20
FNAME ='Raleway'

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
        self.color = color

# PROJECT_ = {
#     "d_komodo": r"Komodo$_{D}$",
#     "s_komodo": r"Komodo$_S$",
#     "d_fvbkv": r"VeriBetrKV$_{D}$",
#     "d_lvbkv": r"VeriBetrKV$_{L}$",
#     "fs_dice": r"DICE$^\star_F$",
#     "fs_vwasm": r"vWasm$_F$",
# } 

GROUP_PLOT_META = {
"d_komodo": GrourpPlotMeta("d_komodo", r"Komodo$_{D}$", COLORS[0]),
"s_komodo": GrourpPlotMeta("s_komodo", r"Komodo$_S$", COLORS[1]),
"d_fvbkv": GrourpPlotMeta("d_fvbkv", r"VeriBetrKV$_{D}$", COLORS[2]),
"d_lvbkv": GrourpPlotMeta("d_lvbkv", r"VeriBetrKV$_{L}$", COLORS[3]),
"fs_dice": GrourpPlotMeta("fs_dice", r"DICE$^\star_F$", COLORS[4]),
"fs_vwasm": GrourpPlotMeta("fs_vwasm", r"vWasm$_F$", COLORS[5]),
}