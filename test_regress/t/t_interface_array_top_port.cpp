// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//*************************************************************************

#include "verilated.h"

#include "TestCheck.h"

#include VM_PREFIX_INCLUDE
#include "Vt_interface_array_top_port_ifc.h"

#define CHECK_EQ(got, exp) TEST_CHECK_EQ(static_cast<uint32_t>(got), static_cast<uint32_t>(exp));

int main(int argc, char** argv) {
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->threads(1);
    Verilated::commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};
    int errors = 0;
    Vt_interface_array_top_port_ifc* c_data[2][3]{
        {topp->c_data__BRA__0__KET____BRA__2__KET__, topp->c_data__BRA__0__KET____BRA__3__KET__,
         topp->c_data__BRA__0__KET____BRA__4__KET__},
        {topp->c_data__BRA__1__KET____BRA__2__KET__, topp->c_data__BRA__1__KET____BRA__3__KET__,
         topp->c_data__BRA__1__KET____BRA__4__KET__}};

    c_data[0][0]->clk = 0U;
    c_data[0][1]->clk = 0U;
    c_data[0][2]->clk = 0U;
    c_data[1][0]->clk = 0U;
    c_data[1][1]->clk = 0U;
    c_data[1][2]->clk = 0U;

    auto tick = [&topp, &c_data]() {
        c_data[0][0]->clk = !c_data[0][0]->clk;
        c_data[0][1]->clk = !c_data[0][1]->clk;
        c_data[0][2]->clk = !c_data[0][2]->clk;
        c_data[1][0]->clk = !c_data[1][0]->clk;
        c_data[1][1]->clk = !c_data[1][1]->clk;
        c_data[1][2]->clk = !c_data[1][2]->clk;
        topp->eval();
    };
    auto reset = [&c_data](uint32_t res) {
        c_data[0][0]->reset = res;
        c_data[0][1]->reset = res;
        c_data[0][2]->reset = res;
        c_data[1][0]->reset = res;
        c_data[1][1]->reset = res;
        c_data[1][2]->reset = res;
    };
    uint32_t posclk = 0U;
    auto check
        = [&errors, &c_data, &posclk](uint32_t exp1 = 0U, uint32_t exp2 = 0U, uint32_t exp3 = 0U,
                                      uint32_t exp4 = 0U, uint32_t exp5 = 0U, uint32_t exp6 = 0U) {
              CHECK_EQ(c_data[0][0]->value, exp1 * posclk);
              CHECK_EQ(c_data[0][1]->value, exp2 * posclk);
              CHECK_EQ(c_data[0][2]->value, exp3 * posclk);
              CHECK_EQ(c_data[1][0]->value, exp4 * posclk);
              CHECK_EQ(c_data[1][1]->value, exp5 * posclk);
              CHECK_EQ(c_data[1][2]->value, exp6 * posclk);
          };

    for (int i = 0; i < 10; i++) tick();
    posclk = 4U;
    check(2U, 3U, 4U, 3U, 4U, 5U);

    reset(1U);
    tick();
    check(0U);

    reset(0U);
    for (int i = 0; i < 15; i++) tick();
    posclk = 7U;
    check(2U, 3U, 4U, 3U, 4U, 5U);
    CHECK_EQ(topp->cyc, 12U);

    topp->final();
    if (errors) {
        puts("FAIL\n");
        return errors;
    }
    puts("*-* All Finished *-*\n");
    return 0;
}
