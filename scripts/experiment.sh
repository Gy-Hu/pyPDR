#!/bin/bash

# Directory containing the cases
CASE_DIR="/data/guangyuh/coding_env/pyPDR/dataset/hwmcc07_tip_aag"

# Output report file
REPORT_FILE="report_down.csv"

# Initialize the report file
echo "Case,Runtime,Result" > $REPORT_FILE

# Function to run a case and record the result
run_case() {
    case_file=$1
    start_time=$(date +%s)
    result=$(timeout 7200s python run.py "$case_file")
    exit_status=$?
    end_time=$(date +%s)
    runtime=$((end_time - start_time))
    
    if [ $exit_status -eq 124 ]; then # exit status 124 is timeout
        result="Timeout"
    elif [ $exit_status -ne 0 ]; then 
        result="Error"
    fi
    
    echo "$(basename "$case_file"),$runtime,$result" >> $REPORT_FILE
}

export -f run_case
export REPORT_FILE

# Run all cases in parallel
find "$CASE_DIR" -type f | parallel run_case

echo "Report generated: $REPORT_FILE"