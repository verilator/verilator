// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include <iostream>

#include VM_PREFIX_INCLUDE

vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{"TOP"}};

    while (main_time <= 100) {
        if (main_time < 20) {
            top->in1a = 5;
            top->in2a = 10;
            top->in1b = 20;
            top->in2b = 30;
        } else if (main_time >= 20 && main_time < 63) {
            top->in1a = 0;
            top->in2a = 5;
            top->in1b = 15;
            top->in2b = 25;
        } else if (main_time > 78) {
            top->in1a = 10;
            top->in2a = 15;
            top->in1b = 25;
            top->in2b = 35;
        }
        top->eval();
        std::cout << "$time: " << main_time << " | "
                  << "Output outa: " << static_cast<int>(top->outa) << " | "
                  << "Output outb: " << static_cast<int>(top->outb) << std::endl;
        ++main_time;
    }
    top->final();
    printf("*-* All Finished *-*\n");
    return 0;
}
