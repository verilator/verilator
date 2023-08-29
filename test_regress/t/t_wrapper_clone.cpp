//
// DESCRIPTION: Verilator: Verilog Test module for the atClone API
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Yinan Xu.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <unistd.h>

#include <sys/wait.h>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

#include VM_PREFIX_INCLUDE

// Check we properly define the version integer
#if VERILATOR_VERSION_INTEGER < 5015000  // Added in 5.015
#error "VERILATOR_VERSION_INTEGER not set"
#endif

double sc_time_stamp() { return 0; }

// Note: Since pthread_atfork accepts only function pointers,
// we are using a static variable for the TOP just for a simple example.
// Without using pthread_atfork, the user can instead manually call
// prepareClone and atClone before and after calling fork.
static VM_PREFIX* top;
static auto prepareClone = [](){ top->prepareClone(); };
static auto atClone = [](){ top->atClone(); };

void single_cycle(VM_PREFIX* top) {
    top->clock = 1;
    top->eval();

    top->clock = 0;
    top->eval();
}

int main(int argc, char** argv) {
    VerilatedContext* contextp = new VerilatedContext;
    top = new VM_PREFIX{contextp};
    pthread_atfork(prepareClone, atClone, atClone);

    top->reset = 1;
    top->is_parent = 0;
    for (int i = 0; i < 5; i++) { single_cycle(top); }

    top->reset = 0;
    while (!contextp->gotFinish()) {
        single_cycle(top);

        if (top->do_clone) {
            int pid = fork();
            if (pid < 0) {
                printf("fork failed\n");
            } else if (pid == 0) {
                printf("child: here we go\n");
            } else {
                while (wait(NULL) > 0)
                    ;
                printf("parent: here we go\n");
                top->is_parent = 1;
            }
        }
    }

    top->final();

    delete top;
    delete contextp;

    return 0;
}
