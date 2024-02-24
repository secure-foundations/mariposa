
from utils.system_utils import san_check
from utils.analysis_utils import percent

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
            san_check(self._allow_unknown, 
                    f"[ERROR] unknown category {cat}")
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

    def print_status(self, skip_empty=False):
        from tabulate import tabulate
        assert self.finalized
        table = [["category", "count", "percentage"]]
        for c, i in self._items.items():
            if skip_empty and i.count == 0:
                continue
            table.append([c, i.count, f"{round(i.percent, 2)} %"])
        # sort table by percentage
        table = [table[0]] + sorted(table[1:], key=lambda x: x[2], reverse=True)
        table.append(["total", self.total, "100.00 %"])
        print(tabulate(table, headers="firstrow", 
                       tablefmt="github", floatfmt=".2f"))

    def __san_check_comparison(self, other):
        assert self.finalized and other.finalized

        san_check(self.keys().intersection(other.keys()) != set(),
            "comparison with no common categories!")
        
        san_check(self.tally.intersection(other.tally) != set(),
            "comparison with no common items!")

    def get_migration_status(self, that):
        self.__san_check_comparison(that)
        san_check(that.tally.issubset(self.tally), 
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