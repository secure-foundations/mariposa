def find_verus_query(file):
    with open(file) as f:
        lines = f.readlines()
        last_func_def = 0
        last_func_decl = 0
        last_func_term = 0
        lines = list(map(lambda x: x.strip(), lines))
        precise_location = ""
        for i, line in enumerate(lines):
            # check if comment exists under ;; MODULE: comment for precise location
            if line.startswith("(set-info :comment \";; MODULE"):
                # if Fuel comment, ignore
                if lines[i+1] != '(set-info :comment ";; Fuel")':
                    # if so, keep track of the next line
                    precise_location = lines[i+1]
           # find the last Function-Def, Function-Decl-Check-Recommends, and Function-Termination comments
            if line.startswith("(set-info :comment \";; Function-Def"):
                last_func_def = i
            elif line.startswith("(set-info :comment \";; Function-Decl-Check-Recommends"):
                last_func_decl = i
            elif line.startswith("(set-info :comment \";; Function-Termination"):
                last_func_term = i
        # get type, name, and location (from lowest of the three comments above)
        type_and_name_index = max(last_func_def, last_func_decl, last_func_term) 
        type_and_name = lines[type_and_name_index]
        location = lines[type_and_name_index+1]

        # pull out the function type, name, location, and precise location if it exists
        query_type = type_and_name.split(" ")[3]
        name = type_and_name.split(" ")[4][:-2]
        location = location.split(" ")[3] + " " + location.split(" ")[4]
        if precise_location != "":
            precise_location = precise_location.split(" ")[3] + " " + precise_location.split(" ")[4]
        return (query_type, name, location, precise_location)
