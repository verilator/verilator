// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//*************************************************************************

#include "verilated.h"

#include "TestCheck.h"

#include VM_PREFIX_INCLUDE
#include "Vt_interface_top_port2_inner_if.h"
#include "Vt_interface_top_port2_outer_if.h"
#include "Vt_interface_top_port2_virt_if.h"

#define CHECK_EQ(got, exp) TEST_CHECK_EQ(static_cast<uint32_t>(got), static_cast<uint32_t>(exp));

int main(int argc, char** argv) {
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->threads(1);
    Verilated::commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};
    int errors = 0;
    topp->outer->clk = 0U;
    auto tick = [&topp]() {
        topp->outer->clk = !topp->outer->clk;
        topp->eval();
    };
    topp->outer->a = 0U;
    tick();
    tick();
    CHECK_EQ(topp->outer->inner->a, 0U);

    CHECK_EQ(topp->outer->inner->vif->v, 1U);

    topp->outer->a = 1U;
    tick();
    tick();
    CHECK_EQ(topp->outer->inner->a, 1U);

    topp->outer->a = 0U;
    tick();
    tick();
    CHECK_EQ(topp->outer->inner->a, 0U);

    topp->final();
    if (errors) {
        puts("FAIL\n");
        return errors;
    }
    puts("*-* All Finished *-*\n");
    return 0;
}
