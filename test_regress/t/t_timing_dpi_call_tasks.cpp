// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include <cstdio>
#include <cstdlib>
#include <svdpi.h>

#ifdef VERILATOR
#include "verilated.h"
#include "verilated_dpi_call.h"

static VlProcess* callerp = nullptr;
#endif

#ifdef __cplusplus
extern "C" {
#endif

extern void export_nested_suspendable_task(unsigned int i, unsigned int* o);
extern void export_suspendable_task(unsigned int i, unsigned int* o);
extern void export_nonsuspendable_task(unsigned int i, unsigned int* o);

int dpi_import1(unsigned int* o) {
#ifdef VERILATOR
    callerp = VlProcess::currentp();
    if (!callerp) std::abort();
    if (VlDpiCall::current()->process().get() != callerp) std::abort();
#endif
    static unsigned int n = 0;
    export_nested_suspendable_task(1, &n);
    *o = n;
    return 0;
}

int dpi_import2(unsigned int* o) {
#ifdef VERILATOR
    // The second import must restore the caller's process after the first export suspended.
    if (VlProcess::currentp() != callerp) std::abort();
    if (VlDpiCall::current()->process().get() != callerp) std::abort();
#endif
    static unsigned int n = 0;
    export_suspendable_task(2, &n);
    *o = n;
    return 0;
}

int dpi_import3(unsigned int* o) {
    static unsigned int n = 0;
    export_nonsuspendable_task(3, &n);
    *o = n;
    return 0;
}

#ifdef __cplusplus
}
#endif
