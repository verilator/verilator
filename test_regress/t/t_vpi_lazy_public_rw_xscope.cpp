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

#include "Vt_vpi_lazy_public_rw_xscope.h"
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_xscope> topp{
        new Vt_vpi_lazy_public_rw_xscope{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    vpiHandle p0cy = mustFind("t.p0.uc.cy");
    vpiHandle p0py = mustFind("t.p0.py");
    vpiHandle p1cy = mustFind("t.p1.uc.cy");
    vpiHandle p1py = mustFind("t.p1.py");
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
        // Anti-aliasing: the two parent/child instances must not share storage.
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
    Verilated::fatalOnVpiError(false);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x77;
    // Reconstructed (same-scope) signal: read-only, put_value must fail.
    if (vpi_put_value(p0cy, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.p0.uc.cy unexpectedly succeeded\n");
        ++errors;
    }
    Verilated::fatalOnVpiError(true);
    checkInt("t.p0.uc.cy (unchanged)", p0cy, childCy(0x30));
    checkInt("t.p1.uc.cy (unaffected)", p1cy, childCy(0x50));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
