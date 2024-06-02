// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2021 by Wilson Snyder and Marlon James. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Setup multiple one-time callbacks with different time delays.
// Ensure they are not called before the delay has elapsed.

#ifdef IS_VPI

#include "vpi_user.h"

#include <cstdlib>

#else

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE

#endif

#include "TestSimulator.h"
#include "TestVpi.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>

typedef struct {
    PLI_UINT32 count;
    PLI_UINT32* exp_times;
    PLI_UINT32 number_of_exp_times;
} cb_stats;

static cb_stats CallbackStats[cbAtEndOfSimTime + 1];

bool got_error = false;

static vpiHandle ValueHandle, ToggleHandle, ClockHandle;

#ifdef TEST_VERBOSE
bool verbose = true;
#else
bool verbose = false;
#endif

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", __FILE__, __LINE__); \
        got_error = true; \
        return __LINE__; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        got_error = true; \
        return __LINE__; \
    }

#define STRINGIFY_CB_CASE(_cb) \
    case _cb: return #_cb

static const char* cb_reason_to_string(int cb_name) {
    switch (cb_name) {
        STRINGIFY_CB_CASE(cbAtStartOfSimTime);
        STRINGIFY_CB_CASE(cbReadWriteSynch);
        STRINGIFY_CB_CASE(cbReadOnlySynch);
        STRINGIFY_CB_CASE(cbNextSimTime);
        STRINGIFY_CB_CASE(cbStartOfSimulation);
        STRINGIFY_CB_CASE(cbEndOfSimulation);
        STRINGIFY_CB_CASE(cbAtEndOfSimTime);
    default: return "Unsupported callback";
    }
}

#undef STRINGIFY_CB_CASE

bool cb_time_is_delay(int cb_name) {
    // For some callbacks, time is interpreted as a delay from current time
    // instead of an absolute time
    if (cb_name == cbReadOnlySynch || cb_name == cbReadWriteSynch) { return true; }
    return false;
}

// forward declaration
static PLI_INT32 TheCallback(s_cb_data* data);

static PLI_INT32 AtEndOfSimTimeCallback(s_cb_data* data) {
    s_vpi_time t;

    cb_stats* stats = &CallbackStats[data->reason];

    t.type = vpiSimTime;
    vpi_get_time(0, &t);

    if (verbose) vpi_printf(const_cast<char*>("- [@%d] AtEndOfSimTime Callback\n"), t.low);

    CHECK_RESULT(t.low, stats->exp_times[stats->count]);
    stats->count += 1;

    s_cb_data cb_data;
    s_vpi_time time = {vpiSimTime, 0, 417, 0};  // non-zero time to check that it's ignored
    cb_data.time = &time;
    cb_data.reason = cbNextSimTime;
    cb_data.cb_rtn = TheCallback;
    vpiHandle Handle = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(Handle);

    return 0;
}

static PLI_INT32 TheCallback(s_cb_data* data) {
    s_vpi_time t;

    cb_stats* stats = &CallbackStats[data->reason];

    t.type = vpiSimTime;
    vpi_get_time(0, &t);

    if (verbose) {
        vpi_printf(const_cast<char*>("- [@%d] %s Callback\n"), t.low,
                   cb_reason_to_string(data->reason));
    }

    CHECK_RESULT(t.low, stats->exp_times[stats->count]);
    stats->count += 1;

    if (stats->count >= stats->number_of_exp_times) return 0;

    s_cb_data cb_data;
    PLI_UINT32 next_time;

    if (data->reason == cbNextSimTime) {
        // if a cbNextSimTime calback is scheduled from
        // another cbNextSimTime callback, it will
        // be called in the same timestep, so we need
        // to delay registering
        next_time = t.low;
        cb_data.reason = cbAtEndOfSimTime;
        cb_data.cb_rtn = AtEndOfSimTimeCallback;
    } else {
        next_time = stats->exp_times[stats->count];
        if (cb_time_is_delay(data->reason)) { next_time -= t.low; }
        cb_data.reason = data->reason;
        cb_data.cb_rtn = TheCallback;
    }

    if (verbose) {
        vpi_printf(const_cast<char*>("- [@%d] Registering %s Callback with time = %d\n"), t.low,
                   cb_reason_to_string(cb_data.reason), next_time);
    }

    s_vpi_time time = {vpiSimTime, 0, next_time, 0};
    cb_data.time = &time;
    vpiHandle Handle = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(Handle);

    return 0;
}

static PLI_INT32 StartOfSimulationCallback(s_cb_data* data) {
    s_cb_data cb_data;
    s_vpi_time timerec = {vpiSimTime, 0, 0, 0};

    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);

    if (verbose) vpi_printf(const_cast<char*>("- [@%d] cbStartOfSimulation Callback\n"), t.low);

    CHECK_RESULT(t.low, CallbackStats[data->reason].exp_times[0]);
    CallbackStats[data->reason].count += 1;

    cb_data.time = &timerec;
    cb_data.value = 0;
    cb_data.user_data = 0;
    cb_data.obj = 0;
    cb_data.cb_rtn = TheCallback;

    CallbackStats[cbAtStartOfSimTime].exp_times = new PLI_UINT32[3]{5, 15, 20};
    CallbackStats[cbAtStartOfSimTime].number_of_exp_times = 3;
    timerec.low = 5;
    cb_data.reason = cbAtStartOfSimTime;
    vpiHandle ASOSHandle = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(ASOSHandle);

    CallbackStats[cbReadWriteSynch].exp_times = new PLI_UINT32[3]{6, 16, 21};
    CallbackStats[cbReadWriteSynch].number_of_exp_times = 3;
    timerec.low = 6;
    cb_data.reason = cbReadWriteSynch;
    vpiHandle RWHandle = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(RWHandle);

    CallbackStats[cbReadOnlySynch].exp_times = new PLI_UINT32[3]{7, 17, 22};
    CallbackStats[cbReadOnlySynch].number_of_exp_times = 3;
    timerec.low = 7;
    cb_data.reason = cbReadOnlySynch;
    vpiHandle ROHandle = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(ROHandle);

    CallbackStats[cbNextSimTime].exp_times = new PLI_UINT32[9]{5, 6, 7, 15, 16, 17, 20, 21, 22};
    CallbackStats[cbNextSimTime].number_of_exp_times = 9;
    timerec.low = 8;
    cb_data.reason = cbNextSimTime;
    vpiHandle NSTHandle = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(NSTHandle);

    CallbackStats[cbAtEndOfSimTime].exp_times = new PLI_UINT32[8]{5, 6, 7, 15, 16, 17, 20, 21};
    CallbackStats[cbAtEndOfSimTime].number_of_exp_times = 8;

    return (0);
}

static int EndOfSimulationCallback(p_cb_data cb_data) {
    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);

    (void)cb_data;  // Unused

    if (verbose) vpi_printf(const_cast<char*>("- [@%d] cbEndOfSimulation Callback\n"), t.low);

    CHECK_RESULT(t.low, CallbackStats[cbEndOfSimulation].exp_times[0]);
    CallbackStats[cbEndOfSimulation].count += 1;

    CHECK_RESULT(CallbackStats[cbStartOfSimulation].count, 1);
    CHECK_RESULT(CallbackStats[cbAtStartOfSimTime].count, 3);
    CHECK_RESULT(CallbackStats[cbNextSimTime].count, 9);
    CHECK_RESULT(CallbackStats[cbReadWriteSynch].count, 3);
    CHECK_RESULT(CallbackStats[cbReadOnlySynch].count, 3);
    CHECK_RESULT(CallbackStats[cbAtEndOfSimTime].count, 8);
    CHECK_RESULT(CallbackStats[cbEndOfSimulation].count, 1);

    if (!got_error) { printf("*-* All Finished *-*\n"); }
    return 0;
}

// cver entry
static void VPIRegister(void) {
    // Clear stats
    for (int cb = 1; cb <= cbAtEndOfSimTime; cb++) { CallbackStats[cb].count = 0; }
    CallbackStats[cbStartOfSimulation].exp_times = new PLI_UINT32(0);
    CallbackStats[cbEndOfSimulation].exp_times = new PLI_UINT32(22);
    s_cb_data cb_data;
    s_vpi_time timerec = {vpiSuppressTime, 0, 0, 0};

    cb_data.time = &timerec;
    cb_data.value = 0;
    cb_data.user_data = 0;
    cb_data.obj = 0;
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = StartOfSimulationCallback;

    vpi_register_cb(&cb_data);

    cb_data.reason = cbEndOfSimulation;
    cb_data.cb_rtn = EndOfSimulationCallback;
    vpi_register_cb(&cb_data);
}

#ifdef IS_VPI

// icarus entry
void (*vlog_startup_routines[])(void) = {VPIRegister, 0};

#else

int main(int argc, char** argv, char** env) {
    double sim_time = 100;
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    bool cbs_called;
    contextp->commandArgs(argc, argv);
    // contextp->debug(9);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

    topp->clk = 1;

    // StartOfSimulationCallback(nullptr);
    VPIRegister();

    VerilatedVpi::callCbs(cbStartOfSimulation);

    topp->clk = 0;
    topp->eval();

    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        VerilatedVpi::callTimedCbs();
        VerilatedVpi::callCbs(cbNextSimTime);
        VerilatedVpi::callCbs(cbAtStartOfSimTime);

        topp->eval();

        VerilatedVpi::callValueCbs();
        VerilatedVpi::callCbs(cbReadWriteSynch);
        VerilatedVpi::callCbs(cbReadOnlySynch);
        VerilatedVpi::callCbs(cbAtEndOfSimTime);

        const uint64_t next_time = VerilatedVpi::cbNextDeadline();
        if (next_time != -1) contextp->time(next_time);
        if (verbose)
            vpi_printf(const_cast<char*>("- [@%" PRId64 "] time change\n"), contextp->time());
        if (next_time == -1 && !contextp->gotFinish()) {
            if (got_error) {
                vl_stop(__FILE__, __LINE__, "TOP-cpp");
            } else {
                VerilatedVpi::callCbs(cbEndOfSimulation);
                contextp->gotFinish(true);
            }
        }

        // Count updates on rising edge, so cycle through falling edge as well
        topp->clk = !topp->clk;
        topp->eval();
        topp->clk = !topp->clk;
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    exit(0L);
}

#endif
