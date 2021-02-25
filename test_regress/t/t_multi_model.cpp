//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020-2021 by Andreas Kuster.
// SPDX-License-Identifier: CC0-1.0
//

#include <iostream>
#include <thread>

#include <verilated.h>

#include "Vt_multi_model__Syms.h"
#include "Vt_multi_model.h"

double sc_time_stamp() {
    return 0;
}  // TODO: we should find a way to remove (or auto-include) this line of code)

void sim0(Vt_multi_model* top0) {

    // setup remaining parameters
    top0->trace_number
        = 0;  // should be fixed with this PR: !! interferes with the main_time from top1 !!
    top0->reset_clock();

    // reset
    top0->clk_i = 0;
    top0->rst_i = 1;
    top0->eval();
    top0->tick();
    top0->clk_i = 1;
    top0->eval();
    top0->tick();
    top0->rst_i = 0;
    top0->clk_i = 0;
    top0->eval();

    // simulate until done
    while (!top0->gotFinish()) {  // should be fixed with this PR: !! will not always work properly
                                  // due to a race condition with top1 !!

        // increment time
        top0->tick();
        std::cout << "[top0] time=" << top0->main_time() << std::endl;

        // toggle clk_i
        top0->clk_i = !top0->clk_i;

        // evaluate model
        top0->eval();
    }
}

void sim1(Vt_multi_model* top1) {

    // setup remaining parameters
    top1->trace_number = 1;
    top1->reset_clock();  // should be fixed with this PR: !! interferes with the main_time from
                          // top0 !!

    // reset
    top1->clk_i = 0;
    top1->rst_i = 1;
    top1->eval();
    top1->tick();
    top1->clk_i = 1;
    top1->eval();
    top1->tick();
    top1->rst_i = 0;
    top1->clk_i = 0;
    top1->eval();

    // simulate until done
    while (!top1->gotFinish()) {  // should be fixed with this PR: !! will not always work properly
                                  // due to a race condition with top0 !!

        // increment time
        top1->tick();
        std::cout << "[top1] time=" << top1->main_time() << std::endl;

        // toggle clk_i
        top1->clk_i = !top1->clk_i;

        // evaluate model
        top1->eval();
    }
}

int main(int argc, char** argv, char** env) {

    // enable tracing
    Verilated::traceEverOn(true);

    // create log directory
    Verilated::mkdir("logs");

    // instantiate verilated design
    std::unique_ptr<Vt_multi_model> top0p{new Vt_multi_model("top0")};
    std::unique_ptr<Vt_multi_model> top1p{new Vt_multi_model("top1")};
    top0p->init_sim_context();
    top1p->init_sim_context();

    // create threads
    std::thread t0(sim0, top0p.get());
    std::thread t1(sim1, top1p.get());

    // wait to finish
    t0.join();
    t1.join();

    // check if both finished
    if (top0p->done_o && top1p->done_o) {
        std::cout << "*-* All Finished *-*" << std::endl;
    } else {
        std::cout << "Error: Early termination!" << std::endl;
    }

    // final model cleanup
    top0p->final();
    top1p->final();

// add coverage
#if VM_COVERAGE
    VerilatedCov::write("logs/coverage.dat");
#endif

    // exit successful
    exit(0);
}
