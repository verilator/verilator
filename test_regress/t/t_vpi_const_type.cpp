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

#ifdef IS_VPI

#include "sv_vpi_user.h"

#include <cstdlib>

#else

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_const_type.h"
#include "Vt_vpi_const_type__Dpi.h"
#include "svdpi.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

extern "C" {
int mon_check() {
#ifdef TEST_VERBOSE
    printf("-mon_check()\n");
#endif

    TestVpiHandle intHandle = vpi_handle_by_name((PLI_BYTE8*)"t.intParam", NULL);
    CHECK_RESULT_NZ(intHandle)
    PLI_INT32 intConstType = vpi_get(vpiConstType, intHandle);
    CHECK_RESULT(intConstType, vpiDecConst)
    const char* intConstTypeStr = vpi_get_str(vpiConstType, intHandle);
    CHECK_RESULT_CSTR(intConstTypeStr, "vpiDecConst")

    TestVpiHandle realHandle = vpi_handle_by_name((PLI_BYTE8*)"t.realParam", NULL);
    CHECK_RESULT_NZ(realHandle)
    PLI_INT32 realConstType = vpi_get(vpiConstType, realHandle);
    CHECK_RESULT(realConstType, vpiRealConst)
    const char* realConstTypeStr = vpi_get_str(vpiConstType, realHandle);
    CHECK_RESULT_CSTR(realConstTypeStr, "vpiRealConst")

    TestVpiHandle strHandle = vpi_handle_by_name((PLI_BYTE8*)"t.strParam", NULL);
    CHECK_RESULT_NZ(strHandle)
    PLI_INT32 strConstType = vpi_get(vpiConstType, strHandle);
    CHECK_RESULT(strConstType, vpiStringConst)
    const char* strConstTypeStr = vpi_get_str(vpiConstType, strHandle);
    CHECK_RESULT_CSTR(strConstTypeStr, "vpiStringConst")

    // t.signal_rd is not constant, and should error on a write
    TestVpiHandle sigHandle = vpi_handle_by_name((PLI_BYTE8*)"t.signal_rd", NULL);
    CHECK_RESULT_NZ(sigHandle)
    PLI_INT32 sigConstType = vpi_get(vpiConstType, sigHandle);
    CHECK_RESULT(sigConstType, vpiUndefined)
    const char* sigConstTypeStr = vpi_get_str(vpiConstType, sigHandle);
    CHECK_RESULT_CSTR(sigConstTypeStr, "*undefined*")
    // and should error on a write
    s_vpi_value vpi_value;
    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = 1;
    vpi_put_value(sigHandle, &vpi_value, NULL, vpiNoDelay);
    CHECK_RESULT(vpi_chk_error(nullptr), vpiError);
    // and an intertial write
    vpi_put_value(sigHandle, &vpi_value, NULL, vpiInertialDelay);
    CHECK_RESULT(vpi_chk_error(nullptr), vpiError);

    // t.signal_rw is not constant
    sigHandle = vpi_handle_by_name((PLI_BYTE8*)"t.signal_rw", NULL);
    CHECK_RESULT_NZ(sigHandle)
    sigConstType = vpi_get(vpiConstType, sigHandle);
    CHECK_RESULT(sigConstType, vpiUndefined)
    sigConstTypeStr = vpi_get_str(vpiConstType, sigHandle);
    CHECK_RESULT_CSTR(sigConstTypeStr, "*undefined*")

    // left range of t.signal_rw
    TestVpiHandle leftHandle = vpi_handle(vpiLeftRange, sigHandle);
    CHECK_RESULT_NZ(leftHandle)
    PLI_INT32 leftConstType = vpi_get(vpiConstType, leftHandle);
    CHECK_RESULT(leftConstType, vpiDecConst)

    TestVpiHandle timeHandle = vpi_handle_by_name((PLI_BYTE8*)"t.timeParam", NULL);
    CHECK_RESULT_NZ(timeHandle)
    PLI_INT32 timeConstType = vpi_get(vpiConstType, timeHandle);
    CHECK_RESULT(timeConstType, vpiDecConst)

    return 0;  // Ok
}
}
//======================================================================

#ifdef IS_VPI

static int mon_check_vpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = mon_check();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static s_vpi_systf_data vpi_systf_data[] = {{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$mon_check",
                                             (PLI_INT32(*)(PLI_BYTE8*))mon_check_vpi, 0, 0, 0},
                                            0};

// cver entry
void vpi_compat_bootstrap(void) {
    p_vpi_systf_data systf_data_p;
    systf_data_p = &(vpi_systf_data[0]);
    while (systf_data_p->type != 0) vpi_register_systf(systf_data_p++);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    // We're going to be checking for these errors so don't crash out
    contextp->fatalOnVpiError(0);

    {
        // Construct and destroy
        const std::unique_ptr<VM_PREFIX> topp{
            new VM_PREFIX{contextp.get(),
                          // Note null name - we're flattening it out
                          ""}};
    }

    // Test second construction
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
    tfp->open(STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    topp->eval();
    contextp->timeInc(10);

    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        contextp->timeInc(1);
        topp->eval();
        VerilatedVpi::callValueCbs();
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
    }
    if (!contextp->gotFinish()) {
        vl_fatal(FILENM, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    return 0;
}

#endif
