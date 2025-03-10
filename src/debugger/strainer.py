from enum import Enum
import os
import shutil
from analysis.singleton_analyzer import SingletonAnalyzer
from base.exper_analyzer import ExperAnalyzer
from base.exper import Experiment
from base.factory import FACT
from utils.system_utils import list_smt2_files, log_debug


SOLVER = FACT.get_solver("z3_4_13_0")
VERI_CFG = FACT.get_config("verify")

CFG_10 = FACT.get_config("verus_quick")
CFG_60 = FACT.get_config("default")

QA_10 = FACT.get_analyzer("10sec")
QA_60 = FACT.get_analyzer("60sec")


def get_exp_params(is_verus):
    if is_verus:
        qa = QA_10
        cfg = CFG_10
    else:
        qa = QA_60
        cfg = CFG_60
    return qa, cfg


class DebugStatus(Enum):
    NO_PROOF = "no proof"

    NOT_CREATED = "not created"
    NOT_TESTED = "not yet tested"

    UNFILTERED = "not yet filtered"

    FINISHED_RAW = "filtered finished but not analyzed"
    FIX_FOUND = "fix found"
    FIX_NOT_FOUND = "fix not found"

    ERROR = "some error occurred"

    def is_finished(self):
        return self in {
            DebugStatus.FINISHED_RAW,
            DebugStatus.FIX_FOUND,
            DebugStatus.FIX_NOT_FOUND,
        }


class Strainer:
    def __init__(self, proj_name, is_verus=False):
        self._proj_name = proj_name
        self._is_verus = is_verus
        self._status = None
        self._tested = None
        self._filtered = None
        self.__init_status()

    @property
    def tested_name(self) -> str:
        return self._proj_name

    @property
    def test_dir(self) -> str:
        return f"data/projs/{self.tested_name}/base.z3"

    @property
    def test_db_dir(self) -> str:
        return f"data/dbs/{self.tested_name}/base.z3"

    @property
    def filter_name(self) -> str:
        return self._proj_name + ".filtered"

    @property
    def filter_dir(self) -> str:
        return f"data/projs/{self.filter_name}/base.z3"

    @property
    def filter_db_dir(self) -> str:
        return f"data/dbs/{self.filter_name}/base.z3"

    def __init_status(self):
        if not os.path.exists(self.test_dir):
            log_debug(f"[strainer] dir not found: {self.test_dir}")
            self._status = DebugStatus.NOT_CREATED
            return

        proj = FACT.get_project_by_path(self.test_dir)

        self._status = DebugStatus.NOT_TESTED

        exp = FACT.try_get_exper(proj, VERI_CFG, SOLVER)

        if exp is None:
            return

        if list_smt2_files(self.test_dir) == [] and exp.get_sum_count() == 0:
            # print("????", self.test_dir)
            log_debug(f"[strainer] file not found in {self.test_dir}")
            self._status = DebugStatus.NOT_CREATED
            return

        try:
            self._tested = SingletonAnalyzer(exp, QA_60)
        except Exception as e:
            print("exception: ", e)
            self._status = DebugStatus.ERROR
            return

        self._status = DebugStatus.UNFILTERED

        if not os.path.exists(self.filter_dir):
            return

        qa, cfg = get_exp_params(self._is_verus)

        proj = FACT.get_project_by_path(self.filter_dir)
        
        exp = FACT.try_get_exper(proj, cfg, SOLVER)

        if exp is None:
            return

        try:
            self._filtered = ExperAnalyzer(exp, qa)
        except Exception as e:
            print("exception: ", e)
            self._status = DebugStatus.ERROR
            return

        self._status = DebugStatus.FINISHED_RAW

    @property
    def tested(self) -> ExperAnalyzer:
        return self._tested

    @property
    def filtered(self) -> ExperAnalyzer:
        return self._filtered

    @property
    def status(self) -> DebugStatus:
        return self._status

    def get_dirs(self):
        return [
            self.test_dir,
            self.test_db_dir,
            self.filter_dir,
            self.filter_db_dir,
        ]

    def clear_all(self):
        for d in self.get_dirs():
            if not os.path.exists(d):
                continue
            log_debug(f"[carver] removing {d}")
            shutil.rmtree(d)
