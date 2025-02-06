import subprocess
import os

# Directory containing the files
files_directory = "data/projs/bench_unstable/base.z3"

# Get a list of files in the directory (assuming you only want to process files, not subdirectories)
files = [f for f in os.listdir(files_directory) if os.path.isfile(os.path.join(files_directory, f))]

# The 102 solved proofs in /ocean/projects/cis230065p/ashah12/mariposa_alternative/mariposa
solved_files_1 = ['3ce5c5e4dc', 'f335e72a88', 'adf9eda1ef', 'c5b6c95d49', '87abcdd247', 'eff0b44ea2', '90270fc66a', '667b2b80fe', '4f68aa20b3', 'cbc1128701', '179f62e2d4', 'd75368331e', '43588efb1c', '563f5abfa4', 'fac95e1ef6', '11e4bbf583', '3ed37733c3', '7373c499e2', '93954d4dad', '738511822f', '1ab6690346', '2a3b1202bd', '1d32c4d524', '8be7c5ec27', '26cc7a44c8', '7f39d29669', '085a5fa6a3', '19e7b4a644', '79fffdb8cb', '9f41cf9dd5', '44a2764cf8', '0cce886818', 'f92fbc3fec', 'b9896cbaf6', '3c3d86031e', 'b5d367aaf5', 'e998d08b31', '92bd652a7c', '018a6d3a64', '7e3368fab1', '7af5ba0b16', '61daeac2cb', '2f6a6b82e9', 'e508668090', '383f10cfb6', '1b5eabf811', 'b1b86518f3', 'fa1767e6e3', '75a47c804d', 'b6e82319b9', 'b8ed14e0c5', '3d19b7e2c9', 'b837e52d8b', 'c8a3060122', '4d7e86f7da', '6200b46f8f', '5add81d45d', 'b546a78766', '81f91a69f2', '125461812b', '085408afeb', '0416307c14', 'b100de24e1', '73e0c43c61', 'b5f812a861', 'd64b61f919', '0cfa69df01', '83c57f0bcb', '1673ca97a5', 'd71eeda4cd', 'cca6928c4f', '0c40f30097', '5c1612881d', 'fa733ab6d6', '8e8d83f571', '1d23e345a5', '8909f4c8e6', 'e41d0ee45e', '4680269ef1', 'fc23d57b68', '0cedd72fe1', 'e1c4753770', 'a0c42cc37e', '8852397c03', '09f0c73516', '28672c8a4e', '2a783d134b', '8f383c7db0', '9b9277bc39', '2cbf19182c', '243ec915e0', '926dcc2129', '03df204fcd', 'd4e5e77cbc', '0defc27a3b', 'd01bd917c5', 'f8e63dc317', '5ab30afc32', '9bfdf36ae8', 'c48bc62edc', 'a0a67d231a', '2211f3ba76']

# The 18 solved proofs in /ocean/projects/cis230065p/ashah12/mariposa
solved_files_2 = ['3ce5c5e4dc', 'adf9eda1ef', '667b2b80fe', '1d32c4d524', '79fffdb8cb', 'c8a3060122', 'b100de24e1', '73e0c43c61', '0cfa69df01', '83c57f0bcb', 'cca6928c4f', '1d23e345a5', 'e41d0ee45e', '8852397c03', '8f383c7db0', '9b9277bc39', 'c48bc62edc', 'a9ba4f3553']

def get_name_hash(filename):
    import hashlib
    # TODO: this should probably do fine?
    return hashlib.sha256(filename.encode()).hexdigest()[0:10]

# Iterate over each file_name in the files directory
for file_name in files:

    if get_name_hash("data/projs/bench_unstable/base.z3/" + file_name) in solved_files_1 + solved_files_2:
        print(f"Skipping {file_name}")
        continue
        

    # Construct the full path to the input file
    input_file_path = os.path.join(files_directory, file_name)
    
    # Construct the command
    command = [
        "python3", "src/debugger3.py", 
        "-i", input_file_path,  # Path to the input file
        "--retry-failed", 
        # "--skip-core", 
    ]
    
    try:
        # Run the command
        print(f"Running command for {file_name}...")
        subprocess.run(command, check=True)  # Run the command and raise an error if it fails
        print(f"Successfully ran command for {file_name}")
    except subprocess.CalledProcessError as e:
        # Handle command failure
        print(f"Command failed for {file_name}. Error: {e}")

    # cleaning up garbage
    command = [
        "python3", "src/debugger3.py", 
        "-i", input_file_path,  # Path to the input file
        "--collect-garbage"
    ]
    
    try:
        # Run the command
        print(f"Cleaning garbage for {file_name}...")
        subprocess.run(command, check=True)  # Run the command and raise an error if it fails
        print(f"Successfully cleaned garbage for {file_name}")
    except subprocess.CalledProcessError as e:
        # Handle command failure
        print(f"Could not clean garbage for {file_name}. Error: {e}")


