import matplotlib.pyplot as plt

plt.rcParams['text.usetex'] = True
plt.rcParams["font.family"] = "serif"
plt.rcParams["font.size"] = 14

PROJECT_LABELS = {
    "d_komodo": r"Komodo$_{D}$",
    "s_komodo": r"Komodo$_S$",
    "d_fvbkv": r"VeriBetrKV$_{D}$",
    "d_lvbkv": r"VeriBetrKV$_{L}$",
    "fs_dice": r"DICE$^\star_F$",
    "fs_vwasm": r"vWasm$_F$",
    "d_ironsht": r"IronKV$_D$",
    "v_ironkv": r"IronKV$_V$",
    "v_mimalloc": r"Mimalloc$_V$",
    "v_noderep": r"NodeRep$_V$",
    "v_pagetable": r"PageTable$_V$",
    "v_pmemlog": r"PMemLog$_V$",
    "total": "Total",
} 

PROJECT_COLORS = {
    "d_komodo": "#FFAA33",
    "d_fvbkv": "#800080",
    "d_lvbkv": "#808000",
    "d_ironsht": "#FF0000",
    "fs_vwasm": "#708090",
    "fs_dice":  "#FF4500",
    "v_ironfleet": "#4682B4",
    "v_mimalloc": "#800000",
    "v_noderep": "#DAA520",
    "v_pagetable": "#191970",
    "v_pmemlog": "#008B8B",
}