//
// DESCRIPTION: Verilator: Verilog Test module for prepareClone/atClone APIs
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

double sc_time_stamp() { return 0; }

// Note: Since the pthread_atfork API accepts only function pointers,
// we are using a static variable for the TOP just for a simple example.
// Without using the pthread_atfork API, the user can instead manually call
// prepareClone and atClone before and after calling fork, and topp can be
// allocated dynamically.
static VM_PREFIX* topp = nullptr;
static auto prepareClone = []() { topp->prepareClone(); };
static auto atClone = []() { topp->atClone(); };

void single_cycle(VM_PREFIX* topp) {
    topp->clock = 1;
    topp->eval();

    topp->clock = 0;
    topp->eval();
}

int main(int argc, char** argv) {
    // We disable the buffering for stdout in this test.
    // Redirecting the stdout to files with buffering causes duplicated stdout
    // outputs in both parent and child processes, even if they are actually
    // called before the fork.
    setvbuf(stdout, nullptr, _IONBF, 0);

    VerilatedContext* contextp = new VerilatedContext;
    topp = new VM_PREFIX{contextp};

    // To avoid resource leaks, prepareClone must be called before fork to
    // free all the allocated resources. Though this would bring performance
    // overhead to the parent process, we believe that fork should not be
    // called frequently, and the overhead is minor compared to simulation.
    pthread_atfork(prepareClone, atClone, atClone);

    // If you care about critical performance, prepareClone can be avoided,
    // with atClone being called only at the child process, as follows.
    // It has the same functionality as the previous one, but has memory leaks.
    // According to the sanitizer, 288 bytes are leaked for one fork call.
    // pthread_atfork(nullptr, nullptr, atClone);

    topp->reset = 1;
    topp->is_parent = 0;
    for (int i = 0; i < 5; i++) { single_cycle(topp); }

    topp->reset = 0;
    while (!contextp->gotFinish()) {
        single_cycle(topp);

        if (topp->do_clone) {
            const int pid = fork();
            if (pid < 0) {
                printf("fork failed\n");
            } else if (pid == 0) {
                printf("child: here we go\n");
            } else {
                while (wait(nullptr) > 0)
                    ;
                printf("parent: here we go\n");
                topp->is_parent = 1;
            }
        }
    }

    topp->final();

    VL_DO_DANGLING(delete topp, topp);
    VL_DO_DANGLING(delete contextp, contextp);

    return 0;
}
