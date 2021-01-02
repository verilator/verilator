//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Andreas Kuster.
// SPDX-License-Identifier: CC0-1.0
//

#include <iostream>
#include <thread>

#include <verilated.h>

#include "Vt_multi_model.h"

vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

void sim0(Vt_multi_model* top0) {

    // setup remaining parameters
    top0->trace_name = "trace0.vcd";
    main_time = 0;  // !! interferes with the main_time from top1 !!

    // reset
    top0->clk_i = 0;
    top0->rst_i = 1;
    top0->eval();
    main_time++;
    top0->clk_i = 1;
    top0->eval();
    main_time++;
    top0->rst_i = 0;
    top0->clk_i = 0;
    top0->eval();

    // simulate until done
    while (!Verilated::gotFinish()) {  // !! will not always work properly due to a race condition
                                       // with top1 !!

        // increment time
        main_time++;

        // toggle clk_i
        top0->clk_i = !top0->clk_i;

        // evaluate model
        top0->eval();
    }
}

void sim1(Vt_multi_model* top1) {

    // setup remaining parameters
    top1->trace_name = "trace1.vcd";
    main_time = 0;  // !! interferes with the main_time from top0 !!

    // reset
    top1->clk_i = 0;
    top1->rst_i = 1;
    top1->eval();
    main_time++;
    top1->clk_i = 1;
    top1->eval();
    main_time++;
    top1->rst_i = 0;
    top1->clk_i = 0;
    top1->eval();

    // simulate until done
    while (!Verilated::gotFinish()) {  // !! will not always work properly due to a race condition
                                       // with top0 !!

        // increment time
        main_time++;
        std::cout << "time=" << main_time << std::endl;
        // toggle clk_i
        top1->clk_i = !top1->clk_i;

        // evaluate model
        top1->eval();
    }
}

int main(int argc, char** argv, char** env) {

    // enable tracing
    Verilated::traceEverOn(true);

    // instantiate verilated design
    Vt_multi_model* top0 = new Vt_multi_model;
    Vt_multi_model* top1 = new Vt_multi_model;

    // create threads
    std::thread t0(sim0, top0);
    std::thread t1(sim1, top1);

    // wait to finish
    t0.join();
    t1.join();

    // check if both finished
    if (top0->done_o && top1->done_o) {
        std::cout << "*-* All Finished *-*" << std::endl;
    } else {
        std::cout << "Error: Early termination!" << std::endl;
    }

    // cleanup
    top0->final();
    delete top0;
    top1->final();
    delete top1;

    // exit successful
    exit(0);
}
