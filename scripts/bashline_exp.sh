#!/bin/bash

# Set the directory containing the cases
case_dir="/data/guangyuh/coding_env/pyPDR/dataset/hwmcc07_tip_aag"

# Create CSV file and add title
output_csv="report_ic3ref.csv"
echo "Case,Runtime,Result" > $output_csv

# Function to run a single case
run_case() {
    case=$1
    case_name=$(basename $case)
    
    start_time=$(date +%s)
    result=$(timeout 1800s IC3 < $case 2>&1)
    end_time=$(date +%s)
    
    runtime=$((end_time - start_time))
    
    # Check if the result is empty (indicating a timeout or error)
    if [ -z "$result" ]; then
        result="Timeout"
    fi
    
    # Append results to CSV file
    echo "$case_name,$runtime,$result" >> $output_csv
}

export -f run_case
export output_csv

# Find all cases and run them in parallel
find $case_dir -type f -name "*.aag" | xargs -n 1 -P 0 -I {} bash -c 'run_case "$@"' _ {}

echo "Experiment completed. Results saved to $output_csv."