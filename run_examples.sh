#!/bin/bash

# Script by bachisheo

# Iterate through each file in the directory
for filename in examples/*.tip; do
        # Run the command and capture the exit code
        ./tip -types "$filename" > /dev/null
        exit_code=$?
        # Extract the base filename (without directory)
        testcase=$(basename "$filename")
        # Check if the filename starts with "error"
        if [[ "$testcase" == err_* ]]; then
            # If exit code is non-zero, print an error message
            if [[ $exit_code -eq 0 ]]; then
                echo "Error: $testcase returned a zero exit code."
            else
                echo "Success: $testcase."
            fi
        else
            # If exit code is non zero, Print an error message for other cases
            if [[ $exit_code -ne 0 ]]; then
                echo "Error: $testcase returned a non-zero exit code."
            else
              echo "Success: $testcase."
            fi
        fi
done
