#include "svdpi.h"

#include <stdio.h>

extern "C" {

void sv_add_to_counter(int amount);

// Define the C function that was imported into SystemVerilog
void c_execute_test() {
    printf("[C]  Execution transferred to C environment.\n");

    // Call the SystemVerilog exported function.
    // Because we used 'context' in the import declaration in SV,
    // the simulator knows exactly which instance's 'module_counter' to update.
    printf("[C]  Calling SV function to add 10...\n");
    sv_add_to_counter(10);

    printf("[C]  Calling SV function to add 25...\n");
    sv_add_to_counter(25);

    printf("[C]  Returning control to SystemVerilog.\n");
}

};
