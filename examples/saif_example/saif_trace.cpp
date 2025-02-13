// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_saif_c.h>

#include <memory>

#include "Vcounter.h"

int errors = 0;

unsigned long long main_time = 0;
double sc_time_stamp() { return static_cast<double>(main_time); }

const char* trace_name() {
    static char name[1000];
    VL_SNPRINTF(name, 1000, "simx.saif");
    return name;
}

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    std::unique_ptr<Vcounter> top{new Vcounter};

    std::unique_ptr<VerilatedSaifC> tfp{new VerilatedSaifC};

    static constexpr int SIMULATION_DURATION{199};
    top->trace(tfp.get(), SIMULATION_DURATION);

    tfp->open(trace_name());

    top->clk = 0;

    while (main_time < SIMULATION_DURATION) {
        top->clk = !top->clk;
        top->eval();
        tfp->dump(static_cast<unsigned int>(main_time));
        ++main_time;
    }
    tfp->close();
    top->final();
    tfp.reset();
    top.reset();
    printf("*-* All Finished *-*\n");
    return errors;
}
