import os
import subprocess
import sys

def run_verilator_test(test_name, verilog_file, options=""):
    print(f"\n=== Running {test_name} ===")
    
    # Run Verilator
    verilator_cmd = f"verilator --x-sim -cc {verilog_file} --exe t_{test_name}.cpp -Mdir obj_vlt/{test_name} {options}"
    result = subprocess.run(verilator_cmd, shell=True, capture_output=True, text=True)
    
    if result.returncode != 0:
        print("Verilator compilation failed!")
        print(result.stderr)
        return False
    
    print("Verilator compilation successful.")
    
    # Compile the test
    compile_cmd = f"make -C obj_vlt/{test_name} -f /home/bnielson/git/verilator/test_regress/Makefile_obj --no-print-directory VM_PREFIX=Vt_{test_name} CPPFLAGS_DRIVER=-D{test_name.upper()} {test_name}"
    result = subprocess.run(compile_cmd, shell=True, capture_output=True, text=True)
    
    if result.returncode != 0:
        print("Test compilation failed!")
        print(result.stderr)
        return False
    
    print("Test compilation successful.")
    
    # Run the test
    run_cmd = f"obj_vlt/{test_name}/{test_name}"
    result = subprocess.run(run_cmd, shell=True, capture_output=True, text=True)
    
    print(result.stdout)
    
    if result.returncode != 0:
        print("Test execution failed!")
        print(result.stderr)
        return False
    
    print(f"{test_name} passed!")
    return True

def main():
    tests = [
        {
            "name": "x_sim_edge_cases",
            "verilog": "t_x_sim_edge_cases.v",
            "description": "Edge cases with nested operations, mixed bit widths, arrays, and complex expressions"
        }
    ]
    
    print("Verilator X/Z Four-State Simulation Edge Case Tests")
    print("=" * 60)
    
    passed = 0
    failed = 0
    
    for test in tests:
        print(f\n"\n" + "=" * 40)
        print(f"Test: {test[\"name\"]}")
        print(f"Description: {test[\"description\"]}")
        print("=" * 40)
        
        if run_verilator_test(test["name"], test["verilog"]):
            passed += 1
        else:
            failed += 1
    
    print(f\n"\n" + "=" * 60)
    print(f"Test Summary: {passed} passed, {failed} failed")
    print("=" * 60)
    
    if failed == 0:
        print("✅ All edge case tests passed!")
        return 0
    else:
        print("❌ Some tests failed.")
        return 1

if __name__ == "__main__":
    sys.exit(main())