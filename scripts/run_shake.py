import sys
from utils.shake_utils import *

if __name__ == "__main__":
    shake_partial(sys.argv[2], sys.argv[3], sys.argv[1], int(sys.argv[4]))