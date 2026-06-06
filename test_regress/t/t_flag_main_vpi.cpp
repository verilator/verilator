// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: VPI test library for t_flag_main_vpi
//
// Loaded at runtime via +verilator+vpi+<path> to verify that --binary --vpi
// correctly loads shared libraries and invokes vlog_startup_routines[] (or a
// named bootstrap).  The design drives its own clock; this library only
// observes 'count' via a cbValueChange callback and calls $finish after
// MAX_TICKS edges -- so a successful $finish proves the library was loaded
// and is able to register callbacks and reach signals by name.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

#include <cstdio>
#include <cstdlib>

// Number of count increments to observe before calling $finish
static const int MAX_TICKS = 10;
static vpiHandle s_count_handle = nullptr;

static PLI_INT32 count_change_cb(p_cb_data /*cb_data*/) {
    if (!s_count_handle) return 0;
    s_vpi_value val;
    val.format = vpiIntVal;
    vpi_get_value(s_count_handle, &val);
    if (val.value.integer >= MAX_TICKS) {
        vpi_printf(const_cast<char*>("*-* All Finished *-*\n"));
        vpi_control(vpiFinish, 0);
    }
    return 0;
}

static PLI_INT32 start_of_sim_cb(p_cb_data /*cb_data*/) {
    s_count_handle = vpi_handle_by_name(const_cast<char*>("t.count"), nullptr);
    if (!s_count_handle) {
        vpi_printf(const_cast<char*>("ERROR: cannot find t.count\n"));
        vpi_control(vpiFinish, 1);
        return 0;
    }
    // Observe count: fire a callback whenever it changes
    t_cb_data cb_data;
    s_vpi_time t;
    s_vpi_value val;
    t.type = vpiSuppressTime;
    val.format = vpiSuppressVal;
    cb_data.reason = cbValueChange;
    cb_data.cb_rtn = count_change_cb;
    cb_data.obj = s_count_handle;
    cb_data.time = &t;
    cb_data.value = &val;
    cb_data.user_data = nullptr;
    vpi_register_cb(&cb_data);
    return 0;
}

static PLI_INT32 end_of_sim_cb(p_cb_data /*cb_data*/) {
    vpi_printf(const_cast<char*>("- VPI end of simulation\n"));
    return 0;
}

static void register_callbacks() {
    // cbStartOfSimulation
    t_cb_data cb_data;
    s_vpi_time t;
    t.type = vpiSuppressTime;
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = start_of_sim_cb;
    cb_data.obj = nullptr;
    cb_data.time = &t;
    cb_data.value = nullptr;
    cb_data.user_data = nullptr;
    vpi_register_cb(&cb_data);

    // cbEndOfSimulation
    cb_data.reason = cbEndOfSimulation;
    cb_data.cb_rtn = end_of_sim_cb;
    vpi_register_cb(&cb_data);
}

// IEEE 1800 section 37: vlog_startup_routines[] -- null-terminated array of startup functions
extern "C" {
void (*vlog_startup_routines[])() = {register_callbacks, nullptr};

// Named bootstrap entrypoint -- used when library is loaded as <path>:my_vpi_bootstrap
void my_vpi_bootstrap() { register_callbacks(); }
}
