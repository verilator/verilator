// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Native scheduler differential driver
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"
#if VM_COVERAGE
#include "verilated_cov.h"
#endif
#ifdef NATIVE_SAVE
#include "verilated_save.h"
#endif

#include "Vt_repcut_native.h"
#if VM_VPI
#include "verilated_vpi.h"
#endif
#if VM_TRACE
#include "verilated_vcd_c.h"
#endif
#include <cstdlib>
#include <iostream>

#ifdef NATIVE_FEATURES
#include "Vt_repcut_native__Dpi.h"
#include "svdpi.h"
static unsigned contextCalls = 0;
extern "C" unsigned repcut_native_context(unsigned value) {
    const char* filenamep = nullptr;
    int line = 0;
    if (!svGetScope() || !svGetCallerInfo(&filenamep, &line) || !filenamep || !line) std::abort();
    ++contextCalls;
    return value ^ repcut_native_read();
}
#endif

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(2);
    context.randReset(0);
    context.traceEverOn(true);
    Vt_repcut_native model{&context, ""};
    model.clk_a = 0;
    model.clk_b = 0;
    model.gate = 0;
    model.reset_n = 0;
    model.x = 0;
    model.eval();
#if VM_VPI
    vpiHandle input = vpi_handle_by_name(const_cast<char*>("TOP.x"), nullptr);
    vpiHandle output = vpi_handle_by_name(const_cast<char*>("TOP.a"), nullptr);
    if (!input || !output) {
        std::cerr << "Missing VPI handles: input=" << input << " output=" << output << '\n';
        std::abort();
    }
#endif
#if VM_TRACE
    VerilatedVcdC trace;
    model.trace(&trace, 99);
    trace.open(argv[1]);
#endif
    unsigned rng = 0x391ba;
    for (unsigned step = 0; step < 1024; ++step) {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        model.clk_a = (rng >> 20) & 1;
        model.clk_b = (rng >> 21) & 1;
        model.gate = (rng >> 22) & 1;
        model.reset_n = step > 1 && step % 29;
#if VM_VPI
        s_vpi_value value;
        value.format = vpiIntVal;
        value.value.integer = rng & 0x7fff;
        vpi_put_value(input, &value, nullptr, vpiNoDelay);
#else
        model.x = rng & 0x7fff;
#endif
        context.timeInc(1);
        model.eval();
        model.eval();  // No event must not repeat clocked state updates.
        if (context.gotError() || context.gotFinish()) std::abort();
#ifdef NATIVE_SAVE
        if (step == 511) {
            VerilatedSave save;
            save.open(argv[1]);
            save << &context << model;
            save.close();
            for (unsigned warm = 0; warm < 31; ++warm) {
                model.clk_a = warm & 1;
                model.clk_b = (warm >> 1) & 1;
                model.reset_n = warm > 3;
                model.x = (warm * 913) & 0x7fff;
                context.timeInc(1);
                model.eval();
            }
            VerilatedRestore restore;
            restore.open(argv[1]);
            restore >> &context >> model;
            restore.close();
        }
#endif
#if VM_VPI
        vpi_get_value(output, &value);
        if (value.value.integer != model.a) {
            std::cerr << "VPI mismatch at step " << step << ": " << value.value.integer
                      << " != " << model.a << '\n';
            std::abort();
        }
#endif
        std::cout << step << ' ' << model.a << ' ' << model.b << ' ' << model.gated << ' '
                  << model.divided << ' ' << model.mem_out << ' ' << unsigned(model.divider)
                  << '\n';
#if VM_TRACE
        trace.dump(context.time());
#endif
    }
    model.final();
#if VM_COVERAGE
    context.coveragep()->write(argv[1]);
#endif
#ifdef NATIVE_FEATURES
    if (contextCalls < 100) std::abort();
    std::cout << "context_calls " << contextCalls << '\n';
#endif
#if VM_VPI
    vpi_free_object(input);
    vpi_free_object(output);
#endif
#if VM_TRACE
    trace.close();
#endif
    std::cout << "*-* All Finished *-*\n";
}
