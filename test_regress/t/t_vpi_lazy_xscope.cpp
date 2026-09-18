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
#include "vpi_user.h"

#include <cstdint>
#include <cstdio>
#include <memory>
#include <string>

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

uint32_t readInt(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return static_cast<uint32_t>(value.value.integer);
}

void checkInt(const char* name, vpiHandle handle, uint32_t expected) {
    const uint32_t got = readInt(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected 0x%08x, got 0x%08x\n", name, expected, got);
        ++errors;
    }
}

// Reading must not change what the next read returns: a reconstruction resolves when VPI
// reads it, so an observation that moved the answer would be a defect of the caching
void checkStable(const char* name, vpiHandle handle) {
    const uint32_t first = readInt(handle);
    const uint32_t second = readInt(handle);
    if (first != second) {
        std::printf("%%Error: %s read 0x%08x then 0x%08x\n", name, first, second);
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
    if (std::string{value.value.str} != expected) {
        std::printf("%%Error: %s expected '%s', got '%s'\n", name, expected, value.value.str);
        ++errors;
    }
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

    vpiHandle canon = mustFind("t.canon");
    vpiHandle canonr = mustFind("t.canonr");
    vpiHandle pa = mustFind("t.u_a.p");
    vpiHandle pb = mustFind("t.u_b.p");
    vpiHandle pc = mustFind("t.u_c.p");
    vpiHandle pd = mustFind("t.u_d.p");
    vpiHandle qa = mustFind("t.u_a.q");
    vpiHandle qb = mustFind("t.u_b.q");
    vpiHandle qc = mustFind("t.u_c.q");
    vpiHandle qd = mustFind("t.u_d.q");
    vpiHandle rcanonr = mustFind("t.rcanonr");
    vpiHandle scanonr = mustFind("t.scanonr");
    vpiHandle pe = mustFind("t.u_e.p");
    vpiHandle pf = mustFind("t.u_f.p");
    vpiHandle pg = mustFind("t.u_g.p");
    vpiHandle ph = mustFind("t.u_h.p");
    if (errors) return 10;

    uint32_t acc = 0;
    uint32_t cone = 0;
    uint32_t copy = 0;
    const auto step = [&](uint32_t in) {
        topp->in = in;
        cycle();
        acc += in;
        cone = acc ^ 0x5a5a5a5a;
        copy = acc ^ 0xa5a5a5a5;
        checkInt("t.canon", canon, cone);
        checkInt("t.canonr", canonr, copy);
        // Every port tracks its cross-scope driver
        checkInt("t.u_a.p", pa, cone);
        checkInt("t.u_b.p", pb, cone);
        checkInt("t.u_c.p", pc, copy);
        checkInt("t.u_d.p", pd, copy);
        checkInt("t.u_a.q", qa, cone + 7);
        checkInt("t.u_b.q", qb, cone + 7);
        checkInt("t.u_c.q", qc, copy + 7);
        checkInt("t.u_d.q", qd, copy + 7);
        // A real or string driver cannot become a cross-scope copy row, so its ports are
        // retained; either way they must read their driver's value, not a zeroed shadow
        const double rexp = static_cast<double>(acc) + 0.25;
        const char* const sexp = (acc & 1) ? "odd" : "even";
        checkReal("t.rcanonr", rcanonr, rexp);
        checkString("t.scanonr", scanonr, sexp);
        checkReal("t.u_e.p", pe, rexp);
        checkReal("t.u_f.p", pf, rexp);
        checkString("t.u_g.p", pg, sexp);
        checkString("t.u_h.p", ph, sexp);
        checkStable("t.canon", canon);
        checkStable("t.canonr", canonr);
        checkStable("t.u_a.q", qa);
    };

    // Three distinct nets: a deposit into one port is invisible through its sibling and
    // leaves the driver alone, exactly as --public-flat-rw storage does.
    const auto distinctNets = [&](const char* dname, vpiHandle drv, const char* aname,
                                  vpiHandle pA, const char* bname, vpiHandle pB, uint32_t c) {
        const auto tag = [](const char* name, const char* note) {
            return std::string{name} + " (" + note + ")";
        };
        putInt(aname, pA, 0x0badf00d);
        checkInt(tag(aname, "deposit").c_str(), pA, 0x0badf00d);
        checkInt(tag(bname, "unaffected").c_str(), pB, c);
        checkInt(tag(dname, "undisturbed").c_str(), drv, c);

        // ... and the deposit into the sibling does not disturb the first one either
        putInt(bname, pB, 0x00c0ffee);
        checkInt(tag(bname, "deposit").c_str(), pB, 0x00c0ffee);
        checkInt(tag(aname, "still its own").c_str(), pA, 0x0badf00d);
        checkInt(tag(dname, "still undisturbed").c_str(), drv, c);
    };

    step(0x00000001);
    step(0x00000010);
    step(0x00001234);

    distinctNets("t.canon", canon, "t.u_a.p", pa, "t.u_b.p", pb, cone);
    // The next evaluation overwrites both deposits from the driver
    step(0x0000007f);

    distinctNets("t.canonr", canonr, "t.u_c.p", pc, "t.u_d.p", pd, copy);
    step(0x00000003);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
