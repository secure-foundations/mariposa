from utils.system_utils import get_name_hash

file_path = "../files.txt"

# Open the file and iterate through its lines
with open(file_path, "r") as file:
    for line in file:
        file_name = line.strip()
        print(file_name)
        print(get_name_hash(file_name))  # Use strip() to remove trailing newline or whitespace
