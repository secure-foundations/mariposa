import os
import shutil

def categorize_proof_folders(base_path, delete_empty_files=False, delete_empty_folders = False):
    empty_folders = []
    empty_file_folders = []
    proof_folders = []

    if not os.path.exists(base_path):
        print(f"Base path '{base_path}' does not exist.")
        return

    for sub in os.listdir(base_path):
        sub_path = os.path.join(base_path, sub)
        proofs_path = os.path.join(sub_path, "proofs")
        
        if not os.path.isdir(proofs_path):
            continue  # Skip if "proofs" folder does not exist
        
        files = os.listdir(proofs_path)
        if not files:
            empty_folders.append(proofs_path)
            if delete_empty_folders:
                shutil.rmtree(sub_path)
            continue
        
        all_empty = True
        for file in files:
            file_path = os.path.join(proofs_path, file)
            if os.path.isfile(file_path):
                if os.path.getsize(file_path) > 0:
                    if all_empty:
                        proof_folders.append(sub)
                    all_empty = False
                    # break  # No need to check further
                elif delete_empty_files:
                    os.remove(file_path)
        
        if all_empty:
            empty_file_folders.append(proofs_path)
            if delete_empty_folders:
                shutil.rmtree(sub_path)

    print("Empty Folders:")
    print("\n".join(empty_folders) if empty_folders else "None")
    print(f"Size of Empty Folders: {len(empty_folders)}")


    print("\nFolders with only empty files:")
    print("\n".join(empty_file_folders) if empty_file_folders else "None")
    print(f"Size of Empty File Folders: {len(empty_file_folders)}")

    print("\nProof Folders (at least one non-empty file):")
    print("\n".join(proof_folders) if proof_folders else "None")
    print(f"Size of Proof Folders: {len(proof_folders)}")
    print(proof_folders)


if __name__ == "__main__":
    categorize_proof_folders("dbg", delete_empty_files=False, delete_empty_folders=False)
