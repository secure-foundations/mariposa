import subprocess
import os

# Directory containing the files
files_directory = "data/projs/bench_unstable/base.z3"

# Get a list of files in the directory (assuming you only want to process files, not subdirectories)
files = [f for f in os.listdir(files_directory) if os.path.isfile(os.path.join(files_directory, f))]

def get_name_hash(filename):
    import hashlib
    # TODO: this should probably do fine?
    return hashlib.sha256(filename.encode()).hexdigest()[0:10]

def get_folders(path):
    return [f for f in os.listdir(path) if os.path.isdir(os.path.join(path, f))]

folders = get_folders("dbg")

# Iterate over each file_name in the files directory
for file_name in files:

    if get_name_hash("data/projs/bench_unstable/base.z3/" + file_name) in folders:
        print(f"Skipping {file_name}")
        continue
        

    # Construct the full path to the input file
    input_file_path = os.path.join(files_directory, file_name)
    
    # Construct the command
    command = [
        "python3", "src/debugger3.py", 
        "-i", input_file_path,  # Path to the input file
        "--retry-failed", 
        "--skip-core", 
        "--collect-garbage"
    ]
    
    try:
        # Run the command
        print(f"Running command for {file_name}...")
        subprocess.run(command, check=True)  # Run the command and raise an error if it fails
        print(f"Successfully ran command for {file_name}")
    except subprocess.CalledProcessError as e:
        # Handle command failure
        print(f"Command failed for {file_name}. Error: {e}")
