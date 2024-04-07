#!/bin/bash

# Check if exactly two arguments are passed to the script (directory and python script location)
if [[ $# -ne 2 ]]; then
  printf "Usage: $0 <directory_with_smt2_files> <path_to_query_wizard.py>\n" >&2
  exit 1
fi

directory=$1
python_script=$2

# Function to convert smt2 files
convert_smt2() {
  local file=$1
  local python_script=$2
  local dir=$(dirname "$file")
  local filename=$(basename "$file" .smt2)
  local output_file="${dir}/smtlib_${filename}.smt2"

  # Run the Python script with the given input file and output file
  if ! python3 "$python_script" convert-smtlib -i "$file" -o "$output_file" --incremental; then
    printf "Failed to convert file: %s\n" "$file" >&2
    return 1
  fi

  printf "Successfully converted: %s to %s\n" "$file" "$output_file"
}

# Main function
main() {
  # Ensure the directory exists
  if [[ ! -d $directory ]]; then
    printf "Directory does not exist: %s\n" "$directory" >&2
    exit 1
  fi

  # Loop through all .smt2 files in the specified directory
  find "$directory" -type f -name "*.smt2" | while read -r file; do
    convert_smt2 "$file" "$python_script"
  done
}

main
