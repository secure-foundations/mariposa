import sys, os

def split_query_context(query_path):
    lines = open(query_path, "r").readlines()
    main_context = []
    push_indices = []
    check_sat_indices = []

    for i, line in enumerate(lines):
        if line.startswith("(push"):
            push_indices.append(i)
        if line.startswith("(check-sat"):
            check_sat_indices.append(i)
    assert len(check_sat_indices) == 1

    check_sat_index = check_sat_indices[0]

    if len(push_indices) == 0:
        # unusual case
        # take whatever command before check-sat
        main_index = check_sat_index - 1
        sub_index = main_index
    else:
        main_index = push_indices[-1]
        sub_index = main_index + 1

    # ignore everything after check-sat
    lines = lines[:check_sat_index+1]

    main_context = lines[:main_index]
    query_context = lines[sub_index:]

    assert query_context[-1].startswith("(check-sat")

    # add push/pop
    query_context.insert(0, "(push 1)\n")
    query_context.append("(echo \"[INFO] mariposa-quake\")\n")
    query_context.append("(pop 1)\n")

    return main_context, query_context

def do_quake(query_path, output_path, timeout, repeat=4):
    if not os.path.exists(output_path):
        try:
            os.makedirs("/".join(output_path.split("/")[:-1]))
        except:
            pass
    out_file = open(output_path, "w")
    main_context, query_context = split_query_context(query_path)
    out_file.writelines(main_context)
    query_context.insert(1, "(set-option :timeout {})\n".format(timeout * 1000))
    # query_context.insert(-2, "(get-info :all-statistics )\n")

    for _ in range(repeat):
        out_file.write("".join(query_context))

if __name__ == "__main__":
    do_quake(sys.argv[1], sys.argv[2], 2)

