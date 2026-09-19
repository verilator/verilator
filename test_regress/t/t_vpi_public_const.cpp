// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Will Keen
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"
#include "verilated_vpi.h"

#include "TestVpi.h"
#include "Vt_vpi_public_const.h"

#include <memory>

static int get(const char* name) {
    s_vpi_value value;
    value.format = vpiIntVal;
    vpi_get_value(vpi_handle_by_name((PLI_BYTE8*)name, nullptr), &value);
    return value.value.integer;
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top"}};
    topp->eval();
    s_vpi_value value;
    value.format = vpiIntVal;
    value.value.integer = 0;
    vpi_put_value(vpi_handle_by_name((PLI_BYTE8*)"top.t.v", nullptr), &value, nullptr, vpiNoDelay);
    topp->eval();
    CHECK_RESULT(get("top.t.v"), 0);
    CHECK_RESULT(get("top.t.r"), 0);
    printf("*-* All Finished *-*\n");
    return 0;
}
