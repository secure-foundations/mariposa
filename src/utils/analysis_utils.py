import numpy as np

from utils.system_utils import log_check

def is_ratio(x):
    return type(x) == float and 0 < x < 1

def is_percentile(x):
    return 0 <= x <= 100

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
        print(f"items in {name_a} but not in {name_b}")
        for i in diff0:
            print("\t" + i)
        print(f"{len(diff0)} in {name_a} but not in {name_b}")
    if len(diff1) != 0:
        print(f"items in {name_b} but not in {name_a}")
        for i in diff1:
            print("\t" + i)
        print(f"{len(diff1)} in {name_b} but not in {name_a}")

def get_cdf_pts(data):
    n = len(data)
    y = np.arange(n) * 100 / float(n-1)
    return np.vstack((np.sort(data), y))

class PartialCDF:
    def __init__(self, data):
        self.cdf = get_cdf_pts(data)

        self.xs = self.cdf[0]
        self.ys = self.cdf[1]

        self._valid_dps = self.cdf[:,~np.isnan(self.cdf[0])]

        self.valid_max = self._valid_dps[:,-1]
        self.valid_min = self._valid_dps[:,0]
        self.valid_median = self.get_point_by_percent(50, True)

    def get_point_by_percent(self, p, valid_only):
        assert is_percentile(p)
        if valid_only:
            index = np.argmax(self._valid_dps[1] >= p)
            return self._valid_dps[:,index]
        index = np.argmax(self.cdf[1] >= p)
        return self.cdf[:index]

    def get_point_by_value(self, v, valid_only):
        if valid_only:
            # print(np.argmax(self._valid_dps[0] > v))
            index = np.argmax(self._valid_dps[0] > v)
            return self._valid_dps[:,index]
        index = np.argmax(self.cdf[0] > v)
        return self.cdf[:,index]

def tex_fmt_percent(x, suffix=False):
    assert x >= -100 and x <= 100
    res = f"%.1f" % x
    if suffix: res += r"\%"
    assert x >= 0
    return res

def tex_double_column(x):
    return r"\multicolumn{2}{c}{" + x + r"}"

class CatItem:
    def __init__(self, cat, items, percent):
        self.category = cat
        self.items = items
        self.percent = percent
        self.count = len(items)

    def __contains__(self, item):
        return item in self.items
    
    def __len__(self):
        return self.count
    
    def __iter__(self):
        return iter(self.items)

class Categorizer:
    def __init__(self, categories=[]):
        self._items = dict()
        for c in categories:
            self._items[c] = set()
        self._allow_unknown = len(categories) == 0
        self.finalized = False
        self.tally = set()

    def add_item(self, cat, item):
        assert not self.finalized
        if cat not in self._items:
            log_check(self._allow_unknown, f"unknown category {cat}")
            self._items[cat] = set()
        self.tally.add(item)
        self._items[cat].add(item)

    def finalize(self):
        assert not self.finalized
        total = sum([len(i) for i in self._items.values()])
        for c, its in self._items.items():
            if total == 0:
                self._items[c] = CatItem(c, its, 0)
            else:
                self._items[c] = CatItem(c, its, percent(len(its), total))
        # check disjointness
        assert len(self.tally) == total
        self.finalized = True
        self.total = total

    def __getitem__(self, item):
        assert self.finalized
        if item not in self._items:
            return CatItem(item, set(), 0)
        return self._items[item]
    
    def items(self):
        assert self.finalized
        return self._items.items()
    
    def keys(self):
        assert self.finalized
        return set(self._items.keys())

    def __iter__(self):
        assert self.finalized
        return iter(self._items.keys())

    def get_category(self, item):
        assert self.finalized
        for c in self._items:
            if item in self._items[c]:
                return c
        return None
    
    def filter_out(self, allowed):
        assert self.finalized
        new_cats = Categorizer()
        new_total = 0
        new_tally = self.tally - allowed
        for c, its in self._items.items():
            new_cats._items[c] = its.items - allowed
            new_total += len(new_cats._items[c])
        new_cats.total = new_total
        new_cats.tally = new_tally
        new_cats.finalize()
        return new_cats

    def print_status(self, skip_empty=False, title=""):
        from tabulate import tabulate
        assert self.finalized
        if title != "": print(title)

        table = [["category", "count", "percentage"]]
        for c, i in self._items.items():
            if skip_empty and i.count == 0:
                continue
            table.append([str(c), i.count, f"{round(i.percent, 2)} %"])
        # sort table by count
        table = [table[0]] + sorted(table[1:], key=lambda x: x[1], reverse=True)
        table.append(["total", self.total, "100.00 %"])
        print(tabulate(table, headers="firstrow", 
                       tablefmt="github", floatfmt=".2f"))

    def __san_check_comparison(self, other):
        assert self.finalized and other.finalized

        log_check(self.keys().intersection(other.keys()) != set(),
            "comparison with no common categories!")
        
        log_check(self.tally.intersection(other.tally) != set(),
            "comparison with no common items!")

    def get_migration_status(self, that):
        self.__san_check_comparison(that)
        log_check(that.tally.issubset(self.tally), 
            "migration with item this < that!")
        all_cats = self.keys().union(that.keys())
        migrations = dict()
        # CategorizedItems()
        missing = self.tally - that.tally

        for c0 in all_cats:
            mc0 = Categorizer() 
            for c1 in all_cats:
                common = self[c0].items.intersection(that[c1].items)
                if len(common) == 0:
                    continue
                for item in common:
                    mc0.add_item(c1, item)
            common = self[c0].items.intersection(missing)
            for item in common:
                mc0.add_item("missing", item)
            mc0.finalize()

            if mc0.total != 0:
                migrations[c0] = mc0

        return migrations

    # def print_compare_status(self, other, 
    #                          cats=None, skip_empty=False, 
    #                          this_name="this", that_name="that"):
    #     from tabulate import tabulate
    #     self.__san_check_comparison(other)

    #     all_cats = self.keys().union(other.keys())

    #     if cats is None:
    #         cats = all_cats

    #     table = [["category", this_name, "", that_name, ""]]
    #     rows = dict()

    #     for c in all_cats:
    #         this, that = self[c], other[c]
    #         both_zero = this.count == 0 and that.count == 0
    #         if c not in cats:
    #             san_check(both_zero, f"[ERROR] unexpected category {c} is not zero")
    #             continue
    #         if skip_empty and both_zero:
    #             continue
    #         rows[c] = [this.count, f"{tex_fmt_percent(this.percent, True)}",
    #                       that.count, f"{tex_fmt_percent(that.percent, True)}"]
    #     for c in cats:
    #         if c not in rows:
    #             continue
    #         table.append([c] + rows[c])

    #     table.append(["total", self.total, "100.00 %", other.total, "100.00 %"])
    #     print(tabulate(table, headers="firstrow", 
    #                    tablefmt="latex_raw", floatfmt=".2f"))
