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

    with open(path, 'wb+') as f:
        log_debug(f"saving cache at {name}")
        pickle.dump(obj, f)

def load_cache(name):
    if not has_cache(name):
        return None
    path = get_cache_path(name)
    with open(path, 'rb') as f:
        # log_debug(f"loading cache at {name}")
        return pickle.load(f)

def load_cache_or(name, func, clear=False):
    if clear:
        clear_cache(name)

    obj = load_cache(name)
    if obj is None:
        obj = func()
        save_cache(name, obj)
    return obj

def has_cache(name):
    path = get_cache_path(name)
    return os.path.exists(path)

def clear_cache(name):
    path = get_cache_path(name)

    if has_cache(name):
        os.remove(path)