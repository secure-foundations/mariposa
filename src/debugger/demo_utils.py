from enum import Enum
from tabulate import tabulate


class Report:
    def __init__(self):
        self.tested = None
        self.stabilized = None
        self.freq = None
        self.skipped = None

    def print_tested(self):
        print(f"tested ({len(self.tested)}):")
        sorted_tested = self.tested.sort_values(by=["time"])
        print(tabulate(sorted_tested, headers='keys', tablefmt='psql'))

    def print_stabilized(self):
        if len(self.stabilized) == 0:
            print(f"tested {len(self.tested)}, no stabilized queries.")
            return
        print(f"tested {len(self.tested)}, stabilized ({len(self.stabilized)}):")
        print(tabulate(self.stabilized, headers='keys', tablefmt='psql'))

    def print_insted(self):
        print(f"instantiation ({len(self.freq)}):")
        print(tabulate(self.freq, headers='keys', tablefmt='psql'))
        