
#include "verilated.h"
#include "vpi_user.h"

#include VM_PREFIX_INCLUDE

void iterate(vpiHandle root_handle);

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{contextp.get(), ""}};

    iterate(nullptr);

    return 0;
}
