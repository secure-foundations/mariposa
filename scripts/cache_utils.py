import pickle, os

def cache_save(obj, name):
    with open("cache/" + name, 'wb+') as f:
        pickle.dump(obj, f)

def cache_load(name):
    with open("cache/" + name, 'rb') as f:
        return pickle.load(f)

def cache_exists(name):
    return os.path.exists("cache/" + name)
