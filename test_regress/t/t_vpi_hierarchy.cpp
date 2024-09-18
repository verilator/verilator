// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************


#include <iostream>
#include <string_view>

#include "vpi_user.h"
#include "TestVpi.h"

void iterate(TestVpiHandle root_handle) {
    TestVpiHandle module_iter = vpi_iterate(vpiModule, root_handle);
    for (TestVpiHandle handle = vpi_scan(module_iter); handle != nullptr;
         handle = vpi_scan(module_iter)) {
        iterate(handle);
    }

    TestVpiHandle reg_iter = vpi_iterate(vpiReg, root_handle);
    for (TestVpiHandle handle = vpi_scan(reg_iter); handle != nullptr;
         handle = vpi_scan(reg_iter)) {
        const std::string_view name = vpi_get_str(vpiFullName, handle);
        std::cout << name << std::endl;
    }
}

PLI_INT32 start_of_sim(t_cb_data* data) {
    iterate(nullptr);
    return 0;
}

//cver, xcelium entry
void vpi_compat_bootstrap(void) {

    // We're able to call vpi_main() here on Verilator/Xcelium,
    // but Icarus complains (rightfully so)
    s_cb_data cb_data;
    s_vpi_time vpi_time;

    vpi_time.high = 0;
    vpi_time.low = 0;
    vpi_time.type = vpiSimTime;

    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    cb_data.obj = NULL;
    cb_data.time = &vpi_time;
    cb_data.value = NULL;
    cb_data.index = 0;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

// Verilator (via t_vpi_main.cpp), and standard LRM entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
