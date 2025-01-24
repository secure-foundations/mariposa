from utils.system_utils import get_name_hash
from splitter import split_query
import os

file_path = "files.txt"
new_folder_name = "../split_queries"

os.makedirs(new_folder_name, exist_ok=True)


# Open the file and iterate through its lines
with open(file_path, "r") as file:
    total_files = 0
    for line in file:
        file_name = line.strip()
        print(file_name)
        print(get_name_hash(file_name))  # Use strip() to remove trailing newline or whitespace
        folder = f"{new_folder_name}/splitter_{get_name_hash(file_name)}"
        os.makedirs(folder, exist_ok=True)

        file_path = "../../../yizhou7/mariposa/" + file_name
        num_queries = split_query(file_path, folder)
        total_files += num_queries
    print(f"Total number of files {total_files}")






