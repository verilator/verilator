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
#include "verilated_vpi.h"

#include "Vt_vpi_lazy_public_rw_aliasmeta.h"
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

int readInt(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return value.value.integer;
}

void checkInt(const char* name, vpiHandle handle, int expected) {
    const int got = readInt(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, got);
        ++errors;
    }
}

int boundVal(vpiHandle handle, PLI_INT32 relation) {
    vpiHandle bound = vpi_handle(relation, handle);
    if (!bound) return -777;
    return readInt(bound);
}

void checkProp(const char* name, PLI_INT32 got, PLI_INT32 expected, const char* what) {
    if (got != expected) {
        std::printf("%%Error: %s %s expected %0d, got %0d\n", name, what, expected, got);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_aliasmeta> topp{
        new Vt_vpi_lazy_public_rw_aliasmeta{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->in_a = 0;
    topp->in_b = 0;
    topp->eval();
    cycle();
    topp->rst = 0;
    topp->in_a = 0xa5;
    topp->in_b = 0x3c;
    cycle();  // src_a <= 0xa5, src_b <= 0x3c

    vpiHandle aWide = mustFind("t.a_wide");
    vpiHandle aNet = mustFind("t.a_net");
    if (errors) return 10;

    // a_wide is declared [8:1] but retargeted at src_a's [7:0] storage: the row
    // must report the alias's own bounds, not the canonical's.
    checkProp("t.a_wide", boundVal(aWide, vpiLeftRange), 8, "vpiLeftRange");
    checkProp("t.a_wide", boundVal(aWide, vpiRightRange), 1, "vpiRightRange");
    checkProp("t.a_wide", vpi_get(vpiSize, aWide), 8, "vpiSize");

    // a_net keeps its own [7:0] bounds.
    checkProp("t.a_net", boundVal(aNet, vpiLeftRange), 7, "vpiLeftRange");
    checkProp("t.a_net", boundVal(aNet, vpiRightRange), 0, "vpiRightRange");
    checkProp("t.a_net", vpi_get(vpiSize, aNet), 8, "vpiSize");

    // Storage still resolves to the canonical.
    checkInt("t.a_wide", aWide, 0xa5);
    checkInt("t.a_net", aNet, 0x3c);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
