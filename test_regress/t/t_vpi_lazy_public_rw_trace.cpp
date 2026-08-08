// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_lazy_public_rw_trace.h"
#include "vpi_user.h"

#include <cstdio>
#include <memory>

namespace {

int errors = 0;

vpiHandle mustFind(const char* name) {
    vpiHandle handle = vpi_handle_by_name((PLI_BYTE8*)name, nullptr);
    if (!handle) {
        std::printf("%%Error: failed to find %s\n", name);
        ++errors;
    }
    return handle;
}

void checkInt(const char* name, vpiHandle handle, int expected) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    if (value.value.integer != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, value.value.integer);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_trace> topp{
        new Vt_vpi_lazy_public_rw_trace{contextp.get(), ""}};

#if VM_TRACE
    contextp->traceEverOn(true);
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    uint64_t simTime = 0;
    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
#if VM_TRACE
        tfp->dump(simTime++);
#endif
        topp->clk = 1;
        topp->eval();
#if VM_TRACE
        tfp->dump(simTime++);
#endif
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
#if VM_TRACE
    tfp->dump(simTime++);
#endif
    cycle();
    topp->rst = 0;

    vpiHandle keeph = mustFind("t.keep");
    vpiHandle cmbh = mustFind("t.cmb");
    vpiHandle alias1h = mustFind("t.alias1");
    if (errors) return 10;

    int keep = 0;  // value after reset
    for (int i = 0; i < 4; ++i) {
        cycle();
        keep = (keep + 0x3) & 0x7f;
        checkInt("t.keep", keeph, keep);
        checkInt("t.cmb", cmbh, (keep + 0x1) & 0x7f);
        checkInt("t.alias1", alias1h, keep);
    }

    topp->final();
#if VM_TRACE
    tfp->dump(simTime++);
    tfp->close();
#endif

    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
