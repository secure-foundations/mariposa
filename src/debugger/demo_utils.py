from enum import Enum
from tabulate import tabulate


class Report:
    def __init__(self):
        self.tested = None
        self.stabilized = None
        self.freq = None
        self.skipped = None

    def print_tested(self):
        print(f"Tested ({len(self.tested)}):")
        sorted_tested = self.tested.sort_values(by=["time"])
        print(tabulate(sorted_tested, headers='keys', tablefmt='psql'))

    def print_stabilized(self):
        print(f"Stabilized ({len(self.stabilized)}):")
        sorted_stabilized = self.stabilized.sort_values(by=["time"])
        print(tabulate(sorted_stabilized, headers='keys', tablefmt='psql'))

    def print_insted(self, extend=False):
        print(f"Instantiation ({len(self.freq)}):")
        if not extend:
            print(tabulate(self.freq, headers='keys', tablefmt='psql'))
            return

        extended = self.freq.merge(self.tested, on="qname")
        extended["stabilized"] = extended["qname"].isin(self.stabilized["qname"])
        extended = extended.sort_values(by="trace_count", ascending=False)
        extended = extended[["qname", "trace_count", "stabilized", "action", "time", "result", "edit_path"]]
        print(tabulate(extended, headers='keys', tablefmt='psql'))
        