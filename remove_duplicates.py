#!/usr/bin/env python3
import re

def remove_duplicates(input_file, output_file):
    with open(input_file, 'r') as f:
        lines = f.readlines()

    output_lines = []
    seen_functions = set()
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Check if this is a function definition
        func_match = re.match(r'\s*(static|inline)?\s+\w+\s+(\w+)_4STATE_(\w+)\s*\(', line)
        if func_match:
            func_name = f"{func_match.group(2)}_4STATE_{func_match.group(3)}"
            
            # Check if we've seen this function before
            if func_name in seen_functions:
                # Skip this duplicate function
                # Find the end of this function
                while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                    i += 1
                # Skip the closing brace/line
                if i < len(lines):
                    i += 1
                continue
            else:
                seen_functions.add(func_name)
                output_lines.append(line)
                i += 1
        else:
            # Check for other patterns of duplicates
            # _vl4_anyXZ_* functions
            anyxz_match = re.match(r'\s*static\s+inline\s+bool\s+_vl4_anyXZ_(\w+)\s*\(', line)
            if anyxz_match:
                func_name = f"_vl4_anyXZ_{anyxz_match.group(1)}"
                if func_name in seen_functions:
                    while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                        i += 1
                    if i < len(lines):
                        i += 1
                    continue
                else:
                    seen_functions.add(func_name)
                    output_lines.append(line)
                    i += 1
            else:
                output_lines.append(line)
                i += 1

    with open(output_file, 'w') as f:
        f.writelines(output_lines)

if __name__ == "__main__":
    input_file = 'verilated_funcs.h'
    output_file = 'verilated_funcs_cleaned.h'
    remove_duplicates(input_file, output_file)
    print(f"Duplicates removed. Saved to {output_file}")
    print(f"Original: {len(open(input_file).readlines())} lines")
    print(f"Cleaned: {len(open(output_file).readlines())} lines")