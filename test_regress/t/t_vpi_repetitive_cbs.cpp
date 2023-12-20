// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2020 by Wilson Snyder and Marlon James. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifdef IS_VPI

#include "vpi_user.h"

#include <cstdlib>

#else

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE
#endif

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

const std::vector<int> cbs_to_test{cbValueChange};

enum CallbackState { PRE_REGISTER, ACTIVE, ACTIVE_AGAIN, REM_REREG_ACTIVE, POST_REMOVE };
const std::vector<CallbackState> cb_states{PRE_REGISTER, ACTIVE, ACTIVE_AGAIN, REM_REREG_ACTIVE,
                                           POST_REMOVE};

#define CB_COUNT cbAtEndOfSimTime + 1
TestVpiHandle vh_registered_cbs[CB_COUNT] = {0};

unsigned int callback_counts[CB_COUNT] = {0};
unsigned int callback_expected_counts[CB_COUNT] = {0};

bool callbacks_called[CB_COUNT] = {false};
bool callbacks_expected_called[CB_COUNT] = {false};

std::vector<int>::const_iterator cb_iter;
std::vector<CallbackState>::const_iterator state_iter;

bool got_error = false;

#ifdef IS_VPI
vpiHandle clk_h;
#endif

#ifdef TEST_VERBOSE
bool verbose = true;
#else
bool verbose = false;
#endif

#ifdef IS_VPI
#define END_TEST \
    vpi_control(vpiStop); \
    return 0;
#else
#define END_TEST return __LINE__;
#endif

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", __FILE__, __LINE__); \
        got_error = true; \
        END_TEST \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        got_error = true; \
        END_TEST \
    }

#define STRINGIFY_CB_CASE(_cb) \
    case _cb: return #_cb

static const char* cb_reason_to_string(int cb_name) {
    switch (cb_name) {
        STRINGIFY_CB_CASE(cbValueChange);
    default: return "Unsupported callback";
    }
}

#undef STRINGIFY_CB_CASE

static int the_callback(p_cb_data cb_data) {
    vpi_printf(const_cast<char*>("     The callback\n"));
    callback_counts[cb_data->reason] = callback_counts[cb_data->reason] + 1;
    return 0;
}

static int register_cb(const int next_state) {
    int cb = *cb_iter;
    t_cb_data cb_data_testcase;
    s_vpi_value v;  // Needed in this scope as is in cb_data
    bzero(&cb_data_testcase, sizeof(cb_data_testcase));
    cb_data_testcase.cb_rtn = the_callback;
    cb_data_testcase.reason = cb;

#ifdef IS_VPI
    TestVpiHandle count_h = vpi_handle_by_name(const_cast<char*>("t.count"),
                                               0);  // Needed in this scope as is in cb_data
#else
    TestVpiHandle count_h = VPI_HANDLE("count");  // Needed in this scope as is in cb_data
#endif
    CHECK_RESULT_NZ(count_h);
    if (cb == cbValueChange) {
        v.format = vpiSuppressVal;

        cb_data_testcase.obj = count_h;
        cb_data_testcase.value = &v;
    }

    // State of callback next time through loop
    if (verbose) vpi_printf(const_cast<char*>("     Updating callback for next loop:\n"));
    switch (next_state) {
    case ACTIVE: {
        if (verbose) {
            vpi_printf(const_cast<char*>("     - Registering callback %s\n"),
                       cb_reason_to_string(cb));
        }
        vh_registered_cbs[cb].release();
        vh_registered_cbs[cb] = vpi_register_cb(&cb_data_testcase);
        break;
    }
    case REM_REREG_ACTIVE: {
        if (verbose) {
            vpi_printf(const_cast<char*>("     - Removing callback %s and re-registering\n"),
                       cb_reason_to_string(cb));
        }
        int ret = vpi_remove_cb(vh_registered_cbs[cb]);
        vh_registered_cbs[cb].freed();
        CHECK_RESULT(ret, 1);
        vh_registered_cbs[cb] = vpi_register_cb(&cb_data_testcase);
        break;
    }
    case POST_REMOVE: {
        if (verbose) {
            vpi_printf(const_cast<char*>("     - Removing callback %s\n"),
                       cb_reason_to_string(cb));
        }
        int ret = vpi_remove_cb(vh_registered_cbs[cb]);
        vh_registered_cbs[cb].freed();
        CHECK_RESULT(ret, 1);
        break;
    }
    default:
        if (verbose) vpi_printf(const_cast<char*>("     - No change\n"));
        break;
    }

    return 0;
}

void reset_expected() {
    for (int idx = 0; idx < CB_COUNT; idx++) { callbacks_expected_called[idx] = false; }
}

void cb_will_be_called(const int cb) {
    callback_expected_counts[cb] = callback_expected_counts[cb] + 1;
    callbacks_expected_called[cb] = true;
}

static int test_callbacks(p_cb_data cb_data) {
    t_cb_data cb_data_testcase;
    bzero(&cb_data_testcase, sizeof(cb_data_testcase));

    if (verbose) vpi_printf(const_cast<char*>("     Checking callback results\n"));

    // Check results from previous loop
    int cb = *cb_iter;

    auto count = callback_counts[cb];
    auto exp_count = callback_expected_counts[cb];
    CHECK_RESULT(count, exp_count);

#if !defined(IS_VPI)
    bool called = callbacks_called[cb];
    bool exp_called = callbacks_expected_called[cb];
    CHECK_RESULT(called, exp_called);
#endif

    // Update expected values based on state of callback in next time through main loop
    reset_expected();

    const int current_state = *state_iter;
    const int next_state = (current_state + 1) % cb_states.size();

    switch (next_state) {
    case PRE_REGISTER:
    case ACTIVE:
    case ACTIVE_AGAIN:
    case REM_REREG_ACTIVE: {
        cb_will_be_called(*cb_iter);
        break;
    }
    default: break;
    }

    int ret = register_cb(next_state);
    if (ret) return ret;

    // Update iterators for next loop
    ++state_iter;
    if (state_iter == cb_states.cend()) {
        ++cb_iter;
        state_iter = cb_states.cbegin();
    }

    // Re-register this cb for next time step
    if (cb_iter != cbs_to_test.cend()) {
        if (verbose) {
            vpi_printf(const_cast<char*>("     Re-registering test_callbacks for next loop\n"));
        }
        t_cb_data cb_data_n;
        bzero(&cb_data_n, sizeof(cb_data_n));
        s_vpi_time t1;

        cb_data_n.reason = cbAfterDelay;
        t1.type = vpiSimTime;
        t1.high = 0;
        t1.low = 10;
        cb_data_n.time = &t1;
        cb_data_n.cb_rtn = test_callbacks;
        TestVpiHandle vh_test_cb = vpi_register_cb(&cb_data_n);
        CHECK_RESULT_NZ(vh_test_cb);
    }

    return ret;
}

#ifdef IS_VPI
static int toggle_clock(p_cb_data data) {
    s_vpi_value val;
    s_vpi_time time = {vpiSimTime, 0, 0, 0};

    val.format = vpiIntVal;
    vpi_get_value(clk_h, &val);
    val.value.integer = !val.value.integer;
    vpi_put_value(clk_h, &val, &time, vpiInertialDelay);

    s_vpi_time cur_time = {vpiSimTime, 0, 0, 0};
    vpi_get_time(0, &cur_time);

    if (cur_time.low < 100 && !got_error) {
        t_cb_data cb_data;
        bzero(&cb_data, sizeof(cb_data));
        time.low = 5;
        cb_data.reason = cbAfterDelay;
        cb_data.time = &time;
        cb_data.cb_rtn = toggle_clock;
        vpi_register_cb(&cb_data);
    }

    return 0;
}
#endif

static int register_test_callback(p_cb_data data) {
    t_cb_data cb_data;
    bzero(&cb_data, sizeof(cb_data));
    s_vpi_time t1;

    if (verbose) vpi_printf(const_cast<char*>("     Registering test_cbs Timed callback\n"));

    cb_data.reason = cbAfterDelay;
    t1.type = vpiSimTime;
    t1.high = 0;
    t1.low = 10;
    cb_data.time = &t1;
    cb_data.cb_rtn = test_callbacks;
    TestVpiHandle vh_test_cb = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh_test_cb);

    cb_iter = cbs_to_test.cbegin();
    state_iter = cb_states.cbegin();

#ifdef IS_VPI
    t1.low = 1;
    cb_data.cb_rtn = toggle_clock;
    TestVpiHandle vh_toggle_cb = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh_toggle_cb);

    clk_h = vpi_handle_by_name(const_cast<char*>("t.clk"), 0);
    CHECK_RESULT_NZ(clk_h);
#endif

    return 0;
}

#ifdef IS_VPI

static int end_of_sim_cb(p_cb_data cb_data) {
    if (!got_error) { fprintf(stdout, "*-* All Finished *-*\n"); }
    return 0;
}

// cver entry
void vpi_compat_bootstrap(void) {
    t_cb_data cb_data;
    bzero(&cb_data, sizeof(cb_data));
    {
        vpi_printf(const_cast<char*>("register start-of-sim callback\n"));
        cb_data.reason = cbStartOfSimulation;
        cb_data.time = 0;
        cb_data.cb_rtn = register_test_callback;
        vpi_register_cb(&cb_data);
    }
    {
        cb_data.reason = cbEndOfSimulation;
        cb_data.time = 0;
        cb_data.cb_rtn = end_of_sim_cb;
        vpi_register_cb(&cb_data);
    }
}
// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 100;
    bool cbs_called;
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

    if (verbose) VL_PRINTF("-- { Sim Time %" PRId64 " } --\n", contextp->time());

    register_test_callback(nullptr);

    topp->eval();
    topp->clk = 0;
    contextp->timeInc(1);

    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        if (verbose) {
            VL_PRINTF("-- { Sim Time %" PRId64 " , Callback %s (%d) , Testcase State %d } --\n",
                      contextp->time(), cb_reason_to_string(*cb_iter), *cb_iter, *state_iter);
        }

        topp->eval();

        for (const auto& i : cbs_to_test) {
            if (verbose) {
                VL_PRINTF("     Calling %s (%d) callbacks\n     >>>>\n", cb_reason_to_string(i),
                          i);
            }
            if (i == cbValueChange) {
                cbs_called = VerilatedVpi::callValueCbs();
            } else {
                cbs_called = VerilatedVpi::callCbs(i);
            }
            if (verbose)
                VL_PRINTF("     <<<<\n     Any callbacks called? %s\n", cbs_called ? "YES" : "NO");
            callbacks_called[i] = cbs_called;
        }

        // Always calling this so we can get code coverage on the Verilator debug routine
        VerilatedVpi::dumpCbs();

        VerilatedVpi::callTimedCbs();

        int64_t next_time = VerilatedVpi::cbNextDeadline();
        contextp->time(next_time);
        if (next_time == -1 && !contextp->gotFinish()) {
            if (verbose)
                VL_PRINTF("-- { Sim Time %" PRId64 " , No more testcases } --\n",
                          contextp->time());
            if (got_error) {
                vl_stop(__FILE__, __LINE__, "TOP-cpp");
            } else {
                VL_PRINTF("*-* All Finished *-*\n");
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

    return 0;
}

#endif
