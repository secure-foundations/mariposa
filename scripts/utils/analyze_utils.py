import numpy as np

from utils.sys_utils import san_check

def is_ratio(x):
    return type(x) == float and 0 < x < 1

def percent(a, b):
    return a * 100 / b

def rd_percent(a, b):
    return round(a * 100 / b, 2)

def rd_percent_str(a, b):
    return f"{rd_percent(a, b)}%"

def category_proportions(categories):
    percentages = dict()
    total = sum([len(i) for i in categories.values()])
    for c, i in categories.items():
        percentages[c] = (len(i), percent(len(i), total))
    return percentages, total

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
    
    def __item__(self, item):
        return self.items[item]
    
    def __iter__(self):
        return iter(self.items)

class CategorizedItems:
    def __init__(self, categories=[]):
        self._items = dict()
        for c in categories:
            self._items[c] = set()
        self._allow_unknown = len(categories) == 0
        self.finalized = False

    def add_item(self, cat, item):
        assert not self.finalized
        if cat not in self._items:
            san_check(self._allow_unknown, 
                    f"[ERROR] unknown category {cat}")
            self._items[cat] = set()
        self._items[cat].add(item)

    def finalize(self):
        assert not self.finalized
        total = sum([len(i) for i in self._items.values()])
        self.tally = set.union(*self._items.values())

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
        return self._items[item]

    def items(self):
        assert self.finalized
        return self._items.items()
    
    def __iter__(self):
        assert self.finalized
        return iter(self._items.keys())

    def get_category(self, item):
        assert self.finalized
        for c in self._items:
            if item in self._items[c]:
                return c
        return None

    def print_status(self, skip_empty=False):
        from tabulate import tabulate
        assert self.finalized
        table = [["category", "count", "percentage"]]
        for c, i in self._items.items():
            if skip_empty and i.count == 0:
                continue
            table.append([c, i.count, i.percent])
        # sort table by percentage
        table = [table[0]] + sorted(table[1:], key=lambda x: x[2], reverse=True)
        table.append(["total", self.total, 100])
        print(tabulate(table, headers="firstrow", 
                       tablefmt="github", floatfmt=".2f"))

def get_cdf_pts(data):
    n = len(data)
    y = np.arange(n) * 100 / float(n) 
    return np.sort(data), np.insert(y[1:], n-1, 100)
