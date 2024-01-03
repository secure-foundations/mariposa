import sys
from utils.shake_utils import *

if __name__ == "__main__":
    action = sys.argv[1]

    if action == "emit-partial":
        emit_shake_partial(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    elif action == "run-exp":
        run_shake_prelim(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    elif action == "load-exp":
        data = load_shake_prelim(sys.argv[2])
        for depth in data:
            print(f"{depth} {data[depth]}")
    elif action == "convert":
        convert_verus_queries_cvc5(sys.argv[2], sys.argv[3])
    else:
        print(f"[ERROR] unknown action: {action}")
        sys.exit(1)
