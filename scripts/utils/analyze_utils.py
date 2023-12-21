import numpy as np

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

class CategorizedItems:
    def __init__(self, categories):
        self._items = dict()

        total = sum([len(i) for i in categories.values()])

        for c, i in categories.items():
            self._items[c] = CatItem(c, i, percent(len(i), total))

        self.tally = set.union(*categories.values())
        # check disjointness
        assert len(self.tally) == total
        self.total = total

    def __getitem__(self, item):
        return self._items[item]

    def items(self):
        return self._items.items()
    
    def __iter__(self):
        return iter(self._items.keys())

    def get_category(self, item):
        for c in self._items:
            if item in self._items[c]:
                return c
        return None

def get_cdf_pts(data):
    n = len(data)
    y = np.arange(n) * 100 / float(n) 
    return np.sort(data), np.insert(y[1:], n-1, 100)
