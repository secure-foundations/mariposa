import os
import subprocess
import re

# Define the directory containing the folders
base_dir = "data/dbs"

# Define the remote base paths and the local base paths
remote_dbg_base_path = "yizhou7@serenity-9900k-9a78.andrew.cmu.edu:/home/yizhou7/mariposa/dbg"
local_dbg_base_path = "/home/amarshah/mariposa_fixed/mariposa/dbg"

remote_proj_base_path = "yizhou7@serenity-9900k-9a78.andrew.cmu.edu:/home/yizhou7/mariposa/data/projs"
local_proj_base_path = "/home/amarshah/mariposa_fixed/mariposa/data/projs"

remote_filtered_base_path = "yizhou7@serenity-9900k-9a78.andrew.cmu.edu:/home/yizhou7/mariposa/data/projs"
local_filtered_base_path = "/home/amarshah/mariposa_fixed/mariposa/data/projs"

# Ensure the local directories exist
os.makedirs(local_dbg_base_path, exist_ok=True)
os.makedirs(local_proj_base_path, exist_ok=True)

# Loop through all folders in the base directory
for folder_name in os.listdir(base_dir):
    # Match folders of the form "singleton_{number}"
    if folder_name.startswith("singleton_") and not folder_name.endswith(".filtered"):
        number = folder_name[len("singleton_"):]
        # First SCP command: Copy dbg files
        remote_dbg_path = f"{remote_dbg_base_path}/{number}"
        local_dbg_path = f"{local_dbg_base_path}"
        dbg_command = ["scp", "-r", remote_dbg_path, local_dbg_path]
        print(f"Running: {' '.join(dbg_command)}")
        try:
            subprocess.run(dbg_command, check=True)
        except subprocess.CalledProcessError as e:
            print(f"Error while running command: {' '.join(dbg_command)}")
            print(e)
        
        # Second SCP command: Copy proj files
        remote_proj_path = f"{remote_proj_base_path}/singleton_{number}"
        local_proj_path = f"{local_proj_base_path}"
        proj_command = ["scp", "-r", remote_proj_path, local_proj_path]
        print(f"Running: {' '.join(proj_command)}")
        try:
            subprocess.run(proj_command, check=True)
        except subprocess.CalledProcessError as e:
            print(f"Error while running command: {' '.join(proj_command)}")
            print(e)

        # Third SCP command: Copy filtered proj files
        remote_filtered_path = f"{remote_filtered_base_path}/singleton_{number}.filtered"
        local_filtered_path = f"{local_filtered_base_path}"
        filtered_command = ["scp", "-r", remote_filtered_path, local_filtered_path]
        print(f"Running: {' '.join(filtered_command)}")
        try:
            subprocess.run(filtered_command, check=True)
        except subprocess.CalledProcessError as e:
            print(f"Error while running command: {' '.join(filtered_command)}")
            print(e)
