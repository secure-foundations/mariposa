import re
import os
import argparse

def find_largest_location_label_number(file_path):
    # Regular expression to match "%%location_label%%" followed by a number
    pattern = re.compile(r"%%location_label%%\s*(\d+)")
    
    max_number = None
    
    # Open and read the file line by line
    with open(file_path, 'r') as file:
        for line in file:
            # Find all matches in the line
            matches = pattern.findall(line)
            # Convert found matches to integers and update max_number
            for match in matches:
                number = int(match)
                if max_number is None or number > max_number:
                    max_number = number

    return max_number

def add_assertions_to_new_file(file_name, new_folder_name, line_offset, i, n):
    # Read the contents of the original file into a list of lines
    with open(file_name, 'r') as file:
        lines = file.readlines()
    
    # Generate the new lines based on the given condition
    new_lines = [f"(assert (not %%location_label%%{j}))\n" for j in range(n+1) if j != i]
    
    # Insert the new lines between the third-last and second-last lines
    insert_position = len(lines) - line_offset
    modified_lines = lines[:insert_position] + new_lines + lines[insert_position:]
    
    # Derive the new file name by trimming the last 5 characters from the original file name
    base_name = os.path.splitext(file_name)[0].split("/")[-1]
    new_file_path = f"{new_folder_name}/{base_name}_{i}.smt2"
    
    os.makedirs(new_folder_name, exist_ok=True)

    # Write the modified lines to the new file
    with open(new_file_path, 'w') as new_file:
        new_file.writelines(modified_lines)
    
    print(f"New file created: {new_file_path}")

# Example usage
line_offset = 1
def split_query(input_file, output_folder):
    largest_number = find_largest_location_label_number(input_file)
    for i in range(largest_number + 1):
        add_assertions_to_new_file(input_file, output_folder, line_offset, i, largest_number)

    return largest_number + 1



def main():
    parser = argparse.ArgumentParser(description="Example Python script with a main function")
    parser.add_argument("--input", type=str, help="Input File")
    parser.add_argument("--output", type=str, help="Output File")
    args = parser.parse_args()

    split_query(args.input, args.output)
    

if __name__ == "__main__":
    main()