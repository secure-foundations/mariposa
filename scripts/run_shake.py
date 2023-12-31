import sys
from utils.shake_utils import *

if __name__ == "__main__":
    action = sys.argv[1]

    if action == "partial":
        shake_partial(sys.argv[2], sys.argv[3], sys.argv[4])
    elif action == "oracle":
        shake_oracle(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]))
    else:
        print(f"[ERROR] unknown action: {action}")
        sys.exit(1)
