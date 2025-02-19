import pickle, os
import pandas as pd

from utils.system_utils import log_debug


def get_cache_path(name):
    return "cache/" + name


def save_cache(name, obj):
    path = get_cache_path(name)
    parent = os.path.dirname(path)

    if not os.path.exists(parent):
        os.makedirs(parent)

    if os.path.exists(path):
        log_debug(f"overwriting cache at {name}")

    with open(path, "wb+") as f:
        log_debug(f"saving cache at {name}")
        pickle.dump(obj, f)


def load_cache(name):
    if not has_cache(name):
        return None
    path = get_cache_path(name)
    try:
        with open(path, "rb") as f:
            # log_debug(f"loading cache at {name}")
            return pickle.load(f)
    except Exception as e:
        log_debug(f"[cache] error loading cache at {name}: {e}")
        os.remove(path)
        return None


def load_cache_or(name, func, clear=False):
    if clear:
        clear_cache(name)

    if obj := load_cache(name):
        return obj

    obj = func()
    save_cache(name, obj)

    return obj


def has_cache(name):
    path = get_cache_path(name)
    return os.path.exists(path)


def clear_cache(name):
    if not has_cache(name):
        return

    path = get_cache_path(name)
    os.remove(path)
