//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020-2021 by Andreas Kuster.
// SPDX-License-Identifier: CC0-1.0
//

#include <verilated.h>
#include <verilated_cov.h>

#include <iostream>
#include <thread>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

#include VM_PREFIX_INCLUDE

// Check we properly define the version integer
#if VERILATOR_VERSION_INTEGER < 4219000  // Added in 4.219
#error "VERILATOR_VERSION_INTEGER not set"
#endif

double sc_time_stamp() { return 0; }

int errors = 0;

VerilatedMutex outputMutex;

#ifdef T_WRAPPER_CONTEXT
#elif defined(T_WRAPPER_CONTEXT_SEQ)
VerilatedMutex sequentialMutex;
#elif defined(T_WRAPPER_CONTEXT_FST)
#else
#error "Unexpected test name"
#endif

void sim(VM_PREFIX* topp) {
#ifdef T_WRAPPER_CONTEXT_SEQ
    // Run each sim sequentially
    const VerilatedLockGuard seqLock(sequentialMutex);
#endif

    VerilatedContext* contextp = topp->contextp();
    // This test created a thread, so need to associate VerilatedContext with it
    Verilated::threadContextp(contextp);

    // reset
    topp->clk = 0;
    topp->rst = 1;
    topp->stop = (topp->trace_number == 0);
    topp->eval();

    contextp->timeInc(1);
    topp->clk = 1;
    topp->eval();

    contextp->timeInc(1);
    topp->rst = 0;
    topp->clk = 0;
    topp->eval();

    // simulate until done
    while (!contextp->gotFinish()) {
        // increment time
        contextp->timeInc(1);

        {
            const VerilatedLockGuard lock(outputMutex);
#ifdef TEST_VERBOSE
            // std::endl needed to flush output before mutex release
            std::cout << "{top" << topp->trace_number
                      << ", ctx=" << reinterpret_cast<void*>(contextp) << "} [" << contextp->time()
                      << "]" << std::endl;
#endif
        }

        // toggle clk
        topp->clk = !topp->clk;

        // evaluate model
        topp->eval();
    }

    std::string filename
        = std::string{VL_STRINGIFY(TEST_OBJ_DIR) "/coverage_"} + topp->name() + ".dat";
    contextp->coveragep()->write(filename.c_str());
}

int main(int argc, char** argv, char** env) {
    // Create contexts
    std::unique_ptr<VerilatedContext> context0p{new VerilatedContext};
    std::unique_ptr<VerilatedContext> context1p{new VerilatedContext};

    // configuration
    context0p->threads(1);
    context1p->threads(1);
    context0p->fatalOnError(false);
    context1p->fatalOnError(false);
    context0p->traceEverOn(true);
    context1p->traceEverOn(true);

    // error number checks
    TEST_CHECK_EQ(context0p->errorCount(), 0);
    TEST_CHECK_EQ(context1p->errorCount(), 0);
    context0p->errorCount(1);
    TEST_CHECK_EQ(context0p->errorCount(), 1);
    context0p->errorCount(0);
    TEST_CHECK_EQ(context0p->errorCount(), 0);

    // instantiate verilated design
    std::unique_ptr<VM_PREFIX> top0p{new VM_PREFIX{context0p.get(), "top0"}};
    std::unique_ptr<VM_PREFIX> top1p{new VM_PREFIX{context1p.get(), "top1"}};

    top0p->trace_number = 0;
    top0p->trace_number = 1;

    std::cout << "Below '%Error: ... Verilog $stop' is expected as part of the test\n";

    // create threads
    std::thread t0(sim, top0p.get());
    std::thread t1(sim, top1p.get());

    // wait to finish
    t0.join();
    t1.join();

    // check if both finished
    bool pass = true;
    if (errors) {
        std::cout << "Error: comparison errors" << std::endl;
        pass = false;
    } else if (top0p->done_o && top1p->done_o) {
        std::cout << "*-* All Finished *-*" << std::endl;
    } else {
        std::cout << "Error: Early termination!" << std::endl;
        pass = false;
    }

    // final model cleanup
    top0p->final();
    top1p->final();

    // exit successful
    return pass ? 0 : 10;
}
