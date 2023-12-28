import pickle, os
import pandas as pd

def get_cache_path(name):
    return "cache/" + name

def save_cache(name, obj):
    path = get_cache_path(name)
    parent = os.path.dirname(path)
    if not os.path.exists(parent):
        os.makedirs(parent)
    with open(path, 'wb+') as f:
        pickle.dump(obj, f)

def load_cache(name):
    path = get_cache_path(name)
    with open(path, 'rb') as f:
        return pickle.load(f)

def has_cache(name):
    path = get_cache_path(name)
    return os.path.exists(path)

def clear_cache(name):
    path = get_cache_path(name)
    os.remove(path)