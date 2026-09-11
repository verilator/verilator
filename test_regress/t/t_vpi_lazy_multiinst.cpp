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

#include "Vt_vpi_lazy_multiinst.h"
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
int childCy(int din) { return m8(din ^ 0xa5); }
int parentPy(int din) { return m8(childCy(din) + 0x03); }

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_multiinst> topp{
        new Vt_vpi_lazy_multiinst{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->din0 = 0;
    topp->din1 = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    // multiinst
    {
        vpiHandle ctrh = mustFind("t.ctr");
        vpiHandle aVal = mustFind("t.if_a.val");
        vpiHandle bVal = mustFind("t.if_b.val");
        vpiHandle cVal = mustFind("t.if_c.val");
        vpiHandle aDer = mustFind("t.if_a.derived");
        vpiHandle bDer = mustFind("t.if_b.derived");
        vpiHandle cDer = mustFind("t.if_c.derived");
        vpiHandle u0Din = mustFind("t.u0.din");
        vpiHandle u0Copy = mustFind("t.u0.din_copy");
        vpiHandle u1Din = mustFind("t.u1.din");
        if (errors) return 10;

        for (int i = 0; i < 4; ++i) {
            cycle();
            const int ctr = readInt(ctrh);
            checkInt("t.if_a.val", aVal, (ctr + 0x1) & 0x7f);
            checkInt("t.if_b.val", bVal, (ctr ^ 0x2a) & 0x7f);
            checkInt("t.if_c.val", cVal, 0x55);
            checkInt("t.if_a.derived", aDer, (((ctr + 0x1) & 0x7f) + 0x1) & 0x7f);
            checkInt("t.if_b.derived", bDer, (((ctr ^ 0x2a) & 0x7f) + 0x1) & 0x7f);
            checkInt("t.if_c.derived", cDer, 0x56);
            checkInt("t.u0.din", u0Din, ctr & 0x3c);
            checkInt("t.u0.din_copy", u0Copy, ctr & 0x3c);
            checkInt("t.u1.din", u1Din, (ctr | 0x03) & 0x7f);
        }

        // A deposit through one alias of a helper target lands in the shared shadow: it reads
        // back through both aliases, leaves the other instance alone, and is recomputed
        const int ctr = readInt(ctrh);
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x2a;
        if (!vpi_put_value(u0Din, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write through alias t.u0.din\n");
            ++errors;
        }
        checkInt("t.u0.din (after put)", u0Din, 0x2a);
        checkInt("t.u0.din_copy (after put)", u0Copy, 0x2a);
        checkInt("t.u1.din (after put)", u1Din, (ctr | 0x03) & 0x7f);
        cycle();
        const int newCtr = readInt(ctrh);
        checkInt("t.u0.din (after eval)", u0Din, newCtr & 0x3c);
        checkInt("t.u0.din_copy (after eval)", u0Copy, newCtr & 0x3c);
    }

    // multiinst2
    {
        vpiHandle ctr2h = mustFind("t.ctr2");
        vpiHandle a0h = mustFind("t.if0.a");
        vpiHandle a1h = mustFind("t.if1.a");
        vpiHandle b0h = mustFind("t.if0.b");
        vpiHandle b1h = mustFind("t.if1.b");
        if (errors) return 10;

        for (int i = 0; i < 4; ++i) {
            cycle();
            const int ctr2 = readInt(ctr2h);
            checkInt("t.if0.a", a0h, ctr2 & 0x7f);
            checkInt("t.if1.a", a1h, (ctr2 + 1) & 0x7f);
            checkInt("t.if0.b", b0h, (~ctr2) & 0x7f);
            checkInt("t.if1.b", b1h, ((ctr2 + 1) ^ 0x55) & 0x7f);
        }
    }

    // xscope
    {
        vpiHandle p0cy = mustFind("t.p0.uc.cy");
        vpiHandle p0py = mustFind("t.p0.py");
        vpiHandle p1cy = mustFind("t.p1.uc.cy");
        vpiHandle p1py = mustFind("t.p1.py");
        // A cross-scope alias of a boundary keeps its own row in its own scope
        vpiHandle p0cflop = mustFind("t.p0.uc.cflop");
        vpiHandle p1cflop = mustFind("t.p1.uc.cflop");
        vpiHandle p0xali = mustFind("t.p0.xali");
        vpiHandle p1xali = mustFind("t.p1.xali");
        if (errors) return 10;

        for (const int base : {0x00, 0x13, 0x40, 0xa5, 0xff}) {
            const int din0 = m8(base);
            const int din1 = m8(base + 0x40);
            topp->din0 = din0;
            topp->din1 = din1;
            cycle();
            checkInt("t.p0.uc.cy", p0cy, childCy(din0));
            checkInt("t.p0.py", p0py, parentPy(din0));
            checkInt("t.p1.uc.cy", p1cy, childCy(din1));
            checkInt("t.p1.py", p1py, parentPy(din1));
            checkInt("t.p0.uc.cflop", p0cflop, m8(din0 ^ 0x5a));
            checkInt("t.p1.uc.cflop", p1cflop, m8(din1 ^ 0x5a));
            // Each instance's alias must read its own scope's canonical, not the other's
            checkInt("t.p0.xali", p0xali, m8(din0 ^ 0x5a));
            checkInt("t.p1.xali", p1xali, m8(din1 ^ 0x5a));
            // The two parent/child instances must not share storage
            if (readInt(p0cy) == readInt(p1cy)) {
                std::printf("%%Error: p0.uc.cy and p1.uc.cy share storage (both %0d)\n",
                            readInt(p0cy));
                ++errors;
            }
            if (readInt(p0py) == readInt(p1py)) {
                std::printf("%%Error: p0.py and p1.py share storage (both %0d)\n", readInt(p0py));
                ++errors;
            }
        }

        topp->din0 = 0x30;
        topp->din1 = 0x50;
        cycle();
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x77;
        // Reconstructed same-scope signal: the deposit is per-instance
        if (!vpi_put_value(p0cy, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on reconstructed t.p0.uc.cy failed\n");
            ++errors;
        }
        checkInt("t.p0.uc.cy (deposit)", p0cy, 0x77);
        checkInt("t.p1.uc.cy (unaffected)", p1cy, childCy(0x50));
        topp->eval();
        checkInt("t.p0.uc.cy (after eval)", p0cy, childCy(0x30));
        checkInt("t.p1.uc.cy (after eval)", p1cy, childCy(0x50));

        // Retained cross-scope alias: the deposit is confined to this instance's storage and
        // the driver re-asserts on the next eval
        wr.value.integer = 0x66;
        if (!vpi_put_value(p0xali, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on retained t.p0.xali failed\n");
            ++errors;
        }
        checkInt("t.p0.xali (deposit)", p0xali, 0x66);
        checkInt("t.p0.uc.cflop (unaffected)", p0cflop, m8(0x30 ^ 0x5a));
        checkInt("t.p1.xali (unaffected)", p1xali, m8(0x50 ^ 0x5a));
        topp->eval();
        checkInt("t.p0.xali (after eval)", p0xali, m8(0x30 ^ 0x5a));
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
