#include "verilated_vpi.h"
#include "verilated.h"
#include "verilatedos.h"
#include "vpi_user.h"

#include <iostream>
#include <memory>
#include <string>

#include VM_PREFIX_INCLUDE
#include VM_PREFIX_ROOT_INCLUDE

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{"top"}};

    vpiHandle vh = vpi_handle_by_name(const_cast<char*>("top.top.multidim_signal"), nullptr);
    s_vpi_value value;
    value.format = vpiIntVal;

    int dims_left[] = {26, 52, 123, 3};
    int dims_right[] = {72, 73, 33, 42};

    // Iterate through the dimensions.
    vpiHandle iter_h = vpi_iterate(vpiRange, vh);
    int i = 0;
    int left;
    int right;
    while (vpiHandle range_h = vpi_scan(iter_h)) {
	vpiHandle lh = vpi_handle(vpiLeftRange, range_h);
        vpi_get_value(lh, &value);
        left = value.value.integer;

        vpiHandle rh = vpi_handle(vpiRightRange, range_h);
        vpi_get_value(rh, &value);
        right = value.value.integer;

        if (left != dims_left[i] || right != dims_right[i]) {
            vl_fatal(__FILE__, __LINE__, "main", (std::string("%Error: Incorrect dimension ") + std::to_string(i)).c_str());
        }

	vpi_free_object(lh);
	vpi_free_object(rh);
	vpi_free_object(range_h);

        i = i + 1;
    }
    vpi_free_object(vh);
    topp->final();

    return 0;
}
