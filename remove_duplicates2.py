#!/usr/bin/env python3
import re

def remove_all_duplicates(input_file, output_file):
    with open(input_file, 'r') as f:
        lines = f.readlines()

    output_lines = []
    seen_functions = set()
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Check for function definitions
        func_match = re.match(r'\s*(static|inline)?\s+\w+\s+(\w+)\s*\(', line)
        if func_match:
            func_name = func_match.group(2)
            
            # Check for specific patterns we want to deduplicate
            if (func_name.startswith("VL_EQ_4STATE_") or 
                func_name.startswith("VL_NEQ_4STATE_") or
                func_name.startswith("_vl4_anyXZ_") or
                func_name.startswith("VL_ADD_4STATE_") or
                func_name.startswith("VL_SUB_4STATE_")):
                
                # Create a signature to identify duplicates
                # For example: VL_EQ_4STATE_C, VL_EQ_4STATE_S, etc. are all the same function
                base_name = func_name.split('_')[0] + "_4STATE"
                if base_name in seen_functions:
                    # Skip this duplicate function
                    while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                        i += 1
                    if i < len(lines):
                        i += 1
                    continue
                else:
                    seen_functions.add(base_name)
                    output_lines.append(line)
                    i += 1
            else:
                output_lines.append(line)
                i += 1
        else:
            output_lines.append(line)
            i += 1

    with open(output_file, 'w') as f:
        f.writelines(output_lines)

if __name__ == "__main__":
    input_file = 'verilated_funcs.h'
    output_file = 'verilated_funcs_cleaned2.h'
    remove_all_duplicates(input_file, output_file)
    print(f"Duplicates removed. Saved to {output_file}")
    print(f"Original: {len(open(input_file).readlines())} lines")
    print(f"Cleaned: {len(open(output_file).readlines())} lines")