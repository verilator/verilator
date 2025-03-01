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

#include "verilated.h"
#include "verilated_vcd_c.h"

#include "Vt_vpi_unimpl.h"
#include "Vt_vpi_unimpl__Dpi.h"
#include "svdpi.h"
// No verilated_vpi.h, make sure can link without it

#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestVpi.h"

unsigned int callback_count = 0;

//======================================================================

int _mon_check_unimpl(p_cb_data cb_data) {
    static TestVpiHandle cb, clk_h;
    vpiHandle handle;
    const char* cp = nullptr;
    if (cb_data) {
        // this is the callback
        s_vpi_error_info info;
        vpi_chk_error(&info);
        callback_count++;
        printf("%%Info: got pli message %s\n", info.message);
    } else {
        // setup and install
        static t_cb_data cb_data;
        clk_h = vpi_handle_by_name((PLI_BYTE8*)"t.clk", NULL);

        cb_data.reason = cbPLIError;
        cb_data.cb_rtn = _mon_check_unimpl;  // this function

        cb = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(cb);

        // now exercise unimplemented fns
        vpi_get_cb_info(cb, NULL);
        CHECK_RESULT(callback_count, 1);

        vpi_register_systf(NULL);
        vpi_get_systf_info(NULL, NULL);
        vpi_handle_multi(0, NULL, NULL);
        vpi_get64(0, NULL);
        vpi_get_delays(NULL, NULL);
        vpi_put_delays(NULL, NULL);
        vpi_get_time(NULL, NULL);
        vpi_mcd_name(0);
        vpi_compare_objects(NULL, NULL);
        vpi_get_data(0, NULL, 0);
        vpi_put_data(0, NULL, 0);
        vpi_get_userdata(NULL);
        vpi_put_userdata(NULL, NULL);
        vpi_handle_by_multi_index(NULL, 0, NULL);
        vpi_control(0);

        s_vpi_time time_s;
        time_s.type = 0;
        vpi_get_time(NULL, &time_s);

        handle = vpi_put_value(NULL, NULL, NULL, 0);
        CHECK_RESULT(handle, 0);

        handle = vpi_handle(0, NULL);
        CHECK_RESULT(handle, 0);

        vpi_iterate(0, NULL);

        handle = vpi_register_cb(NULL);
        CHECK_RESULT(handle, 0);
        s_cb_data cb_data_s;
        cb_data_s.reason = 0;  // Bad
        handle = vpi_register_cb(&cb_data_s);
        CHECK_RESULT(handle, 0);

        (void)vpi_get_str(vpiRange, clk_h);  // Bad type

        // Supported but illegal tests:
        // Various checks that guarded passing NULL handles
        handle = vpi_scan(NULL);
        CHECK_RESULT(handle, 0);
        (void)vpi_get(vpiType, NULL);
        (void)vpi_get(vpiDirection, NULL);
        (void)vpi_get(vpiVector, NULL);
        cp = vpi_get_str(vpiType, NULL);
        CHECK_RESULT_Z(cp);
        vpi_release_handle(NULL);

        printf("End of main test\n");
    }
    return 0;  // Ok
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
    if (int status = _mon_check_unimpl(NULL)) return status;
    return 0;  // Ok
}

//======================================================================

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->commandArgs(argc, argv);
    // contextp->debug(9);
    // We're going to be checking for these errors so don't crash out
    contextp->fatalOnVpiError(0);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

#ifdef VERILATOR
#ifdef TEST_VERBOSE
    contextp->scopesDump();
#endif
#endif

#if VM_TRACE
    contextp->traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    topp->eval();
    topp->clk = 0;
    contextp->timeInc(10);

    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        contextp->timeInc(1);
        topp->eval();
        // VerilatedVpi::callValueCbs();   // Make sure can link without verilated_vpi.h included
        topp->clk = !topp->clk;
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
    }
    if (!callback_count) vl_fatal(FILENM, __LINE__, "main", "%Error: never got callbacks");
    if (!contextp->gotFinish()) {
        vl_fatal(FILENM, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    return 0;
}
