import multiprocessing
import time

from utils.system_utils import log_info


PROC_COUNT = 64

def run_with_pool(func, args, goal=0, time_bound=600):
    success = []
    start_time = time.time()

    pool = multiprocessing.Pool(PROC_COUNT)

    if goal <= 0 or goal > len(args):
        goal = len(args)

    while True:
        if len(success) >= goal:
            log_info(f"[pool] goal reached, {len(success)} successes")
            break

        if len(args) == 0:
            log_info(f"[pool] no more args")
            break

        res = pool.map(func, args[:PROC_COUNT])
        args = args[PROC_COUNT:]
        success += [r for r in res if r is not None]

        time_elapsed = int(time.time() - start_time)

        log_info(
            f"[pool] {len(success)} successes, {time_elapsed}(s) elapsed, {len(args)} jobs left"
        )

        if time_elapsed >= time_bound:
            log_info(f"[pool] time budget exceeded: {time_elapsed}")
            break

    pool.close()
    return success