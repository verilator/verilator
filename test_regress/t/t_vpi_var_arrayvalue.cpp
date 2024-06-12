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

#else

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_var_arrayvalue.h"
#include "Vt_vpi_var_arrayvalue__Dpi.h"

#include "svdpi.h"

#endif

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;
// __FILE__ is too long
#define FILENM "t_vpi_var_arrayvalue.cpp"

#define TEST_MSG \
    if (0) printf

unsigned int main_time = 0;


/*-------------------------------------------
MACRO CHECKERS
-------------------------------------------*/

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

#define CHECK_RESULT_Z(got) \
    if ((got)) { \
        printf("%%Error: %s:%d: GOT = !NULL  EXP = NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

/*-------------------------------------------
TEST FUNCTIONS
-------------------------------------------*/

int _mon_check_get_bad(){
    int index[2] = {0,0};
    TestVpiHandle vh = VPI_HANDLE("bad");
    CHECK_RESULT_NZ(vh);

    vpi_get_value_array(vh,nullptr,index,1);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));

    return 0;
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
#ifdef TEST_VERBOSE
    printf("-mon_check()\n");
#endif
    if(int status = _mon_check_get_bad()) return status;
    // if(int status = _mon_check_get()) return status;
#ifndef IS_VPI
    VerilatedVpi::selfTest();
#endif
    return 0;  // Ok
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

double sc_time_stamp() { return main_time; }
int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

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
    topp->clk = 0;
    main_time += 10;

    while (vl_time_stamp64() < sim_time && !contextp->gotFinish()) {
        main_time += 1;
        VerilatedVpi::doInertialPuts();
        topp->eval();
        VerilatedVpi::callValueCbs();
        topp->clk = !topp->clk;
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(main_time);
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
