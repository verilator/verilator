import re

def remove_manual_duplicates(input_file, output_file):
    with open(input_file, 'r') as f:
        lines = f.readlines()

    output_lines = []
    
    # Keep track of which functions we've seen
    seen_eq = set()
    seen_neq = set()
    seen_anyxz = set()
    seen_add = set()
    seen_sub = set()
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Check for VL_EQ_4STATE functions
        if "VL_EQ_4STATE_" in line:
            func_type = line.split("VL_EQ_4STATE_")[1].split()[0].strip()
            if func_type not in seen_eq:
                seen_eq.add(func_type)
                output_lines.append(line)
                i += 1
            else:
                # Skip this duplicate function
                while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                    i += 1
                if i < len(lines):
                    i += 1
            continue
        
        # Check for VL_NEQ_4STATE functions
        elif "VL_NEQ_4STATE_" in line:
            func_type = line.split("VL_NEQ_4STATE_")[1].split()[0].strip()
            if func_type not in seen_neq:
                seen_neq.add(func_type)
                output_lines.append(line)
                i += 1
            else:
                while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                    i += 1
                if i < len(lines):
                    i += 1
            continue
        
        # Check for _vl4_anyXZ functions
        elif "_vl4_anyXZ_" in line:
            func_type = line.split("_vl4_anyXZ_")[1].split()[0].strip()
            if func_type not in seen_anyxz:
                seen_anyxz.add(func_type)
                output_lines.append(line)
                i += 1
            else:
                while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                    i += 1
                if i < len(lines):
                    i += 1
            continue
        
        # Check for VL_ADD_4STATE functions
        elif "VL_ADD_4STATE_" in line:
            func_type = line.split("VL_ADD_4STATE_")[1].split()[0].strip()
            if func_type not in seen_add:
                seen_add.add(func_type)
                output_lines.append(line)
                i += 1
            else:
                while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                    i += 1
                if i < len(lines):
                    i += 1
            continue
        
        # Check for VL_SUB_4STATE functions
        elif "VL_SUB_4STATE_" in line:
            func_type = line.split("VL_SUB_4STATE_")[1].split()[0].strip()
            if func_type not in seen_sub:
                seen_sub.add(func_type)
                output_lines.append(line)
                i += 1
            else:
                while i < len(lines) and not re.match(r'\s*};?\s*$', lines[i]):
                    i += 1
                if i < len(lines):
                    i += 1
            continue
        
        else:
            output_lines.append(line)
            i += 1

    with open(output_file, 'w') as f:
        f.writelines(output_lines)

if __name__ == "__main__":
    input_file = 'include/verilated_funcs.h'
    output_file = 'include/verilated_funcs_cleaned_manual.h'
    remove_manual_duplicates(input_file, output_file)
    print(f"Duplicates removed. Saved to {output_file}")
    print(f"Original: {len(open(input_file).readlines())} lines")
    print(f"Cleaned: {len(open(output_file).readlines())} lines")