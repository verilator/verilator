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

#include VM_PREFIX_INCLUDE
#include "TestCheck.h"
#include "vpi_user.h"

#include <cstdint>
#include <cstdio>
#include <memory>

int errors = 0;

namespace {

vpiHandle mustFind(const char* name) {
    vpiHandle handle = vpi_handle_by_name((PLI_BYTE8*)name, nullptr);
    TEST_CHECK_NZ_LABEL(name, handle);
    return handle;
}

uint32_t readInt(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return static_cast<uint32_t>(value.value.integer);
}

void checkInt(const char* name, vpiHandle handle, uint32_t expected) {
    const uint32_t got = readInt(handle);
    TEST_CHECK_HEX_EQ_LABEL(name, got, expected);
}

void putInt(const char* name, vpiHandle handle, uint32_t value) {
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = static_cast<PLI_INT32>(value);
    if (!vpi_put_value(handle, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write %s\n", name);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
    };

    topp->clk = 0;
    topp->rst = 1;
    topp->in = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    vpiHandle o_h = mustFind("t.u_src.o");
    vpiHandle cpy_a = mustFind("t.u_src.cpy_a");
    vpiHandle cpy_c = mustFind("t.u_src.cpy_c");
    vpiHandle mix = mustFind("t.u_src.mix");
    vpiHandle obs = mustFind("t.u_src.obs");
    if (errors) return 10;

    uint32_t acc = 0;
    const auto step = [&](uint32_t in) {
        topp->in = in;
        cycle();
        acc += in;
        const uint32_t o = acc ^ 0x5a5a0000;
        // 'o' is a temp of the group, never a target, so its row names its own storage and the
        // model has to keep writing it. Serving its readers a shadow instead, and leaving the
        // storage unpinned, reads zero here for ever.
        checkInt("t.u_src.o", o_h, o);
        // The copies are read before anything that runs 'mix's cone: a row wrongly folded
        // onto 'o's temp shadow is refreshed by that cone and by nothing else, so reading it
        // first is what exposes the stale value.
        checkInt("t.u_src.cpy_a", cpy_a, o);
        checkInt("t.u_src.cpy_c", cpy_c, o);
        checkInt("t.u_src.mix", mix, o + 3);
        checkInt("t.u_src.obs", obs, ((o + 3) ^ o) + o);
        return o;
    };

    step(0x00000001);
    step(0x00000010);
    const uint32_t o = step(0x00001234);

    // Each copy is its own net: a deposit into one is not visible through the other, and the
    // next evaluation overwrites it.
    putInt("t.u_src.cpy_a", cpy_a, 0x0badf00d);
    checkInt("t.u_src.cpy_a (deposit)", cpy_a, 0x0badf00d);
    checkInt("t.u_src.cpy_c (unaffected)", cpy_c, o);

    // A deposit into the temp's own storage is overwritten by the next evaluation, as
    // --public-flat-rw does. Nothing is read between, a deposit into retained storage
    // invalidating every shadow.
    putInt("t.u_src.o", o_h, 0x00000040);

    step(0x0000007f);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
