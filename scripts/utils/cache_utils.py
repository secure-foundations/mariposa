import pickle, os

def save_cache(name, obj):
    with open("cache/" + name, 'wb+') as f:
        pickle.dump(obj, f)

def load_cache(name):
    with open("cache/" + name, 'rb') as f:
        return pickle.load(f)

def has_cache(name):
    return os.path.exists("cache/" + name)

def clear_cache(name):
    os.remove("cache/" + name)