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

#include <cstdio>
#include <memory>

// Referenced from the model's '$c' instrumentation; global so the block-scope
// 'extern int' declarations there resolve.
int vlConsEvals = 0;
int vlQuietEvals = 0;

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

void putInt(const char* name, vpiHandle handle, int value) {
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = value;
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

    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    vpiHandle gatedh = mustFind("t.gated");
    vpiHandle quieth = mustFind("t.quiet");
    vpiHandle consumerh = mustFind("t.consumer");
    vpiHandle quietConsh = mustFind("t.quiet_cons");
    vpiHandle floppedh = mustFind("t.flopped");
    if (errors) return 10;

    int gated = 0;
    for (int i = 0; i < 3; ++i) {
        cycle();
        gated = (gated + 0x3) & 0xff;
        checkInt("t.gated", gatedh, gated);
        checkInt("t.consumer", consumerh, gated ^ 0x5a);
    }

    // A deposit into a retained signal must reach its comb consumer and, next edge, the flop
    const int deposit = 0x21;
    putInt("t.gated", gatedh, deposit);
    checkInt("t.gated (after put)", gatedh, deposit);
    topp->eval();
    checkInt("t.consumer (after deposit eval)", consumerh, deposit ^ 0x5a);
    cycle();
    checkInt("t.flopped (deposit through flop)", floppedh, deposit ^ 0x5a);

    // The RTL driver re-asserts itself once its own inputs move on
    gated = (deposit + 0x3) & 0xff;
    checkInt("t.gated (driver re-asserted)", gatedh, gated);
    checkInt("t.consumer (driver re-asserted)", consumerh, gated ^ 0x5a);

    // A plain eval with no VPI write must not re-run the cone; --public-flat-rw re-runs it
    const int quietBefore = vlQuietEvals;
    const int consBefore = vlConsEvals;
    for (int i = 0; i < 5; ++i) topp->eval();
    const int quietDelta = vlQuietEvals - quietBefore;
    const int consDelta = vlConsEvals - consBefore;
    std::printf("quiet cone evals over 5 idle evals: %0d\n", quietDelta);
    std::printf("consumer cone evals over 5 idle evals: %0d\n", consDelta);
#ifndef VL_TEST_UNGATED
    if (quietDelta != 0 || consDelta != 0) {
        std::printf("%%Error: retained cones re-run on idle eval (quiet=%0d cons=%0d)\n",
                    quietDelta, consDelta);
        ++errors;
    }
#else
    // Eager --public-flat-rw re-runs both cones on every eval, gated or not
    if (quietDelta <= 0 || consDelta <= 0) {
        std::printf("%%Error: eager cones did not re-run on idle eval (quiet=%0d cons=%0d)\n",
                    quietDelta, consDelta);
        ++errors;
    }
#endif

    // Depositing again re-arms the gate
    putInt("t.gated", gatedh, 0x7e);
    topp->eval();
    checkInt("t.consumer (second deposit)", consumerh, 0x7e ^ 0x5a);

#ifndef VL_TEST_UNGATED
    // A deposit re-runs the whole 'settle' region once, so both retained cones advance
    const int consArmBefore = vlConsEvals;
    const int quietArmBefore = vlQuietEvals;
    putInt("t.gated", gatedh, 0x33);
    topp->eval();
    topp->eval();
    topp->eval();
    const int consArmDelta = vlConsEvals - consArmBefore;
    const int quietArmDelta = vlQuietEvals - quietArmBefore;
    if (consArmDelta != 1 || quietArmDelta != 1) {
        std::printf("%%Error: cones ran cons=%0d quiet=%0d times across a deposit and two idle"
                    " evals, expected 1 each\n",
                    consArmDelta, quietArmDelta);
        ++errors;
    }

    // vpiInertialDelay only queues the write; the vpiNoDelay re-entry arms the gate
    s_vpi_value inertialWr{};
    inertialWr.format = vpiIntVal;
    inertialWr.value.integer = 0x44;
    s_vpi_time inertialTime{};
    inertialTime.type = vpiSimTime;
    if (!vpi_put_value(gatedh, &inertialWr, &inertialTime, vpiInertialDelay)) {
        std::printf("%%Error: failed to queue inertial-delay write to t.gated\n");
        ++errors;
    }
    const int consInertialBefore = vlConsEvals;
    const int quietInertialBefore = vlQuietEvals;
    VerilatedVpi::doInertialPuts();
    topp->eval();
    checkInt("t.gated (after inertial delay)", gatedh, 0x44);
    const int consInertialDelta = vlConsEvals - consInertialBefore;
    const int quietInertialDelta = vlQuietEvals - quietInertialBefore;
    if (consInertialDelta != 1 || quietInertialDelta != 1) {
        std::printf("%%Error: cones ran cons=%0d quiet=%0d times after an inertial-delay deposit,"
                    " expected 1 each\n",
                    consInertialDelta, quietInertialDelta);
        ++errors;
    }
#endif

    // 'quiet' is only ever written by the RTL, and still tracks it
    checkInt("t.quiet_cons", quietConsh, (readInt(quieth) + 0x11) & 0xff);
    checkInt("t.consumer (tracks gated)", consumerh, readInt(gatedh) ^ 0x5a);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
