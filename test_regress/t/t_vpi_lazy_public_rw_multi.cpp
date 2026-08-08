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

#include "Vt_vpi_lazy_public_rw_multi.h"
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

int m8(int v) { return v & 0xff; }
int ifaceA(int din) { return m8(din + 0x11); }
int ifaceB(int din) { return m8(ifaceA(din) ^ 0x5a); }
int subS1(int din) { return m8(din + 0x07); }
int subS2(int din) { return m8(subS1(din) + m8(din << 1)); }

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_multi> topp{
        new Vt_vpi_lazy_public_rw_multi{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    vpiHandle if0a = mustFind("t.if0.a");
    vpiHandle if0b = mustFind("t.if0.b");
    vpiHandle if1a = mustFind("t.if1.a");
    vpiHandle if1b = mustFind("t.if1.b");
    vpiHandle u0s1 = mustFind("t.u0.s1");
    vpiHandle u0s2 = mustFind("t.u0.s2");
    vpiHandle u1s1 = mustFind("t.u1.s1");
    vpiHandle u1s2 = mustFind("t.u1.s2");
    if (errors) return 10;

    for (const int base : {0x00, 0x13, 0x40, 0xa5, 0xff}) {
        topp->base = base;
        cycle();
        const int if0din = m8(base);
        const int if1din = m8(base + 0x20);
        const int u0din = m8(base);
        const int u1din = m8(base + 0x30);
        checkInt("t.if0.a", if0a, ifaceA(if0din));
        checkInt("t.if0.b", if0b, ifaceB(if0din));
        checkInt("t.if1.a", if1a, ifaceA(if1din));
        checkInt("t.if1.b", if1b, ifaceB(if1din));
        checkInt("t.u0.s1", u0s1, subS1(u0din));
        checkInt("t.u0.s2", u0s2, subS2(u0din));
        checkInt("t.u1.s1", u1s1, subS1(u1din));
        checkInt("t.u1.s2", u1s2, subS2(u1din));
        // Each instance separate.
        if (readInt(if0a) == readInt(if1a)) {
            std::printf("%%Error: if0.a and if1.a share storage (both %0d)\n", readInt(if0a));
            ++errors;
        }
        if (readInt(u0s2) == readInt(u1s2)) {
            std::printf("%%Error: u0.s2 and u1.s2 share storage (both %0d)\n", readInt(u0s2));
            ++errors;
        }
    }

    topp->base = 0x30;
    cycle();
    Verilated::fatalOnVpiError(false);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x77;
    if (vpi_put_value(if0a, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.if0.a unexpectedly succeeded\n");
        ++errors;
    }
    Verilated::fatalOnVpiError(true);
    checkInt("t.if0.a (unchanged)", if0a, ifaceA(m8(0x30)));
    checkInt("t.if1.a (unaffected)", if1a, ifaceA(m8(0x30 + 0x20)));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
