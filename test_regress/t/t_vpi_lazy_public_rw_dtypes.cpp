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

#include "Vt_vpi_lazy_public_rw_dtypes.h"
#include "vpi_user.h"

#include <cstdio>
#include <cstring>
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

void checkReal(const char* name, vpiHandle handle, double expected) {
    s_vpi_value value{};
    value.format = vpiRealVal;
    vpi_get_value(handle, &value);
    if (value.value.real != expected) {
        std::printf("%%Error: %s expected %g, got %g\n", name, expected, value.value.real);
        ++errors;
    }
}

void checkString(const char* name, vpiHandle handle, const char* expected) {
    s_vpi_value value{};
    value.format = vpiStringVal;
    vpi_get_value(handle, &value);
    if (!value.value.str || std::strcmp(value.value.str, expected) != 0) {
        std::printf("%%Error: %s expected '%s', got '%s'\n", name, expected,
                    value.value.str ? value.value.str : "(null)");
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_dtypes> topp{
        new Vt_vpi_lazy_public_rw_dtypes{contextp.get(), ""}};

    const int in0 = 0x3c;
    topp->in0 = in0;
    topp->clk = 0;
    topp->eval();

    checkReal("t.r_comb", mustFind("t.r_comb"), 1.5);
    checkInt("t.i_comb", mustFind("t.i_comb"), in0 + 1);
    checkInt("t.en_comb", mustFind("t.en_comb"), in0 & 0x3);
    checkString("t.s_var", mustFind("t.s_var"), "hi");
    checkInt("t.v_comb", mustFind("t.v_comb"), (in0 ^ 0x5) & 0x7f);

    checkString("t.s_fmt", mustFind("t.s_fmt"), "v60");  // in0 == 0x3c == 60

    checkInt("t.ps_comb", mustFind("t.ps_comb"), in0);
    const int paFlat = ((in0 & 0xff) << 24) | (((in0 ^ 0xff) & 0xff) << 16)
                       | (((in0 + 1) & 0xff) << 8) | ((in0 - 1) & 0xff);
    checkInt("t.pa_comb", mustFind("t.pa_comb"), paFlat);
    {
        vpiHandle pah = mustFind("t.pa_comb");
        vpiHandle e0 = vpi_handle_by_index(pah, 0);
        if (!e0) {
            std::printf("%%Error: failed to index t.pa_comb[0]\n");
            ++errors;
        } else {
            checkInt("t.pa_comb[0]", e0, (in0 - 1) & 0xff);
        }
    }

    checkInt("t.mem", mustFind("t.mem"), in0);  // element 0
    mustFind("t.us_comb");

    Verilated::fatalOnVpiError(false);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x7;
    if (vpi_put_value(mustFind("t.v_comb"), &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.v_comb unexpectedly succeeded\n");
        ++errors;
    }
    if (vpi_put_value(mustFind("t.ps_comb"), &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.ps_comb unexpectedly succeeded\n");
        ++errors;
    }
    Verilated::fatalOnVpiError(true);

    {
        s_vpi_value uw{};
        uw.format = vpiIntVal;
        uw.value.integer = 0x5a;
        vpiHandle mem0 = vpi_handle_by_index(mustFind("t.mem"), 0);
        if (!mem0 || !vpi_put_value(mem0, &uw, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on retained t.mem[0] failed\n");
            ++errors;
        } else {
            checkInt("t.mem[0] (after write)", mem0, 0x5a);
        }
        vpiHandle usa = vpi_handle_by_name((PLI_BYTE8*)"t.us_comb.a", nullptr);
        if (!usa || !vpi_put_value(usa, &uw, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on retained t.us_comb.a failed\n");
            ++errors;
        } else {
            checkInt("t.us_comb.a (after write)", usa, 0x5a);
        }
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
