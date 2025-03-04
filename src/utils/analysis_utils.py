import numpy as np

from utils.system_utils import log_check


def percent(a, b, rd=2):
    return round(a * 100 / b, rd)


def pprint_percent(a, b, rd=2, latex=False):
    if latex:
        return f"{round(percent(a, b), rd)}\%"
    return f"{round(percent(a, b), rd)}%"


def pprint_subset_percent(a, b, rd=2):
    assert len(a) <= len(b)
    return f"{round(percent(len(a), len(b)), rd)}%"


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
    y = np.arange(n) * 100 / float(n - 1)
    return np.vstack((np.sort(data), y))


class PartialCDF:
    def __init__(self, data):
        self.cdf = get_cdf_pts(data)

        self.xs = self.cdf[0]
        self.ys = self.cdf[1]

        self._valid_dps = self.cdf[:, ~np.isnan(self.cdf[0])]

        self.valid_max = self._valid_dps[:, -1]
        self.valid_min = self._valid_dps[:, 0]
        self.valid_median = self.get_point_by_percent(50, True)

    def get_point_by_percent(self, p, valid_only):
        assert 0 <= p <= 100
        if valid_only:
            index = np.argmax(self._valid_dps[1] >= p)
            return self._valid_dps[:, index]
        index = np.argmax(self.cdf[1] >= p)
        return self.cdf[:index]

    def get_point_by_value(self, v, valid_only):
        if valid_only:
            # print(np.argmax(self._valid_dps[0] > v))
            index = np.argmax(self._valid_dps[0] > v)
            return self._valid_dps[:, index]
        index = np.argmax(self.cdf[0] > v)
        return self.cdf[:, index]


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
                self._items[c] = set()
            else:
                self._items[c] = its
        # check disjointness
        assert len(self.tally) == total
        self.finalized = True
        self.total = total

    def __getitem__(self, item):
        assert self.finalized
        if item not in self._items:
            return set()
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

    def switch_category(self, item, new_cat):
        assert self.finalized
        old_cat = self.get_category(item)
        if old_cat is None:
            return
        self._items[old_cat].remove(item)
        self._items[new_cat].add(item)

    def filter(self, allowed):
        assert self.finalized
        new_cats = Categorizer()
        new_total = 0
        new_tally = self.tally - allowed
        for c, its in self.items():
            new_cats._items[c] = its - allowed
            new_total += len(new_cats._items[c])
        new_cats.total = new_total
        new_cats.tally = new_tally
        new_cats.finalize()
        return new_cats

    def print_status(self, skip_empty=False, title=""):
        from tabulate import tabulate

        assert self.finalized
        if title != "":
            print(title)

        table = [["category", "count", "percentage"]]

        for c, i in self._items.items():
            if skip_empty and len(i) == 0:
                continue
            table.append([str(c), len(i), pprint_subset_percent(i, self.tally)])
        # sort table by count
        table = [table[0]] + sorted(table[1:], key=lambda x: x[1], reverse=True)
        table.append(["total", self.total, "100.00 %"])
        print(tabulate(table, headers="firstrow", tablefmt="github", floatfmt=".2f"))

    def analyze_migration(self, that) -> dict:
        log_check(
            self.finalized and that.finalized and that.tally.issubset(self.tally),
            "migration result should be a subset",
        )

        migrations = dict()
        missing = self.tally - that.tally

        for c0 in self.keys():
            mc0 = Categorizer()
            for c1 in that.keys():
                common = self[c0] & that[c1]
                if len(common) == 0:
                    continue
                for item in common:
                    mc0.add_item(c1, item)
            for item in self[c0] & missing:
                mc0.add_item("missing", item)
            mc0.finalize()

            if mc0.total != 0:
                migrations[c0] = mc0

        return migrations


def sort_by_values(d, reverse=True):
    return [
        (k, v) for k, v in sorted(d.items(), key=lambda item: item[1], reverse=reverse)
    ]
