// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//*************************************************************************

#include "verilated.h"

#include "TestCheck.h"

#include VM_PREFIX_INCLUDE
#include "Vt_interface_top_port_ifc.h"

#define CHECK_EQ(got, exp) TEST_CHECK_EQ(static_cast<uint32_t>(got), static_cast<uint32_t>(exp));

int main(int argc, char** argv) {
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->threads(1);
    Verilated::commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};
    int errors = 0;
    topp->c_data->clk = 0U;
    auto tick = [&topp]() {
        topp->c_data->clk = !topp->c_data->clk;
        topp->eval();
    };

    topp->c_data->reset = 0U;
    for (int i = 0; i < 10; i++) tick();
    CHECK_EQ(topp->c_data->value, 4U);

    topp->c_data->reset = 1U;
    tick();
    CHECK_EQ(topp->c_data->value, 0U);

    topp->c_data->reset = 0U;
    for (int i = 0; i < 15; i++) tick();
    CHECK_EQ(topp->c_data->value, 7U);
    CHECK_EQ(topp->cyc, 12U);

    topp->final();
    if (errors) {
        puts("FAIL\n");
        return errors;
    }
    puts("*-* All Finished *-*\n");
    return 0;
}
