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

#include "vpi_user.h"

#include <cstdlib>

#else

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_param.h"
#include "Vt_vpi_param__Dpi.h"
#include "svdpi.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

// __FILE__ is too long
#define FILENM "t_vpi_param.cpp"

#define DEBUG \
    if (0) printf

//======================================================================

#define CHECK_RESULT_VH(got, exp) \
    if ((got) != (exp)) { \
        printf("%%Error: %s:%d: GOT = %p   EXP = %p\n", FILENM, __LINE__, (got), (exp)); \
        return __LINE__; \
    }

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << FILENM << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_HEX(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << FILENM << ":" << __LINE__ << std::hex \
                  << ": GOT = " << (got) << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", FILENM, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR_STRIP(got, exp) CHECK_RESULT_CSTR(got + strspn(got, " "), exp)

int check_param_int(std::string name, PLI_INT32 format, int exp_value, bool verbose) {
    int vpi_type;
    TestVpiHandle param_h;
    s_vpi_value value;
    value.format = format;
    value.value.integer = 0;
    s_vpi_error_info e;
    const char* p;

    vpi_printf((PLI_BYTE8*)"Check parameter %s vpi ...\n", name.c_str());
    param_h = vpi_handle_by_name((PLI_BYTE8*)TestSimulator::rooted(name.c_str()), NULL);
    CHECK_RESULT_NZ(param_h);
    vpi_type = vpi_get(vpiType, param_h);
    CHECK_RESULT(vpi_type, vpiParameter);
    if (verbose) {
        vpi_printf((PLI_BYTE8*)"  vpiType: %s (%d)\n", vpi_get_str(vpiType, param_h), vpi_type);
    }

    // attributes
    p = vpi_get_str(vpiName, param_h);
    CHECK_RESULT_CSTR(p, name.c_str());
    p = vpi_get_str(vpiFullName, param_h);
    CHECK_RESULT_CSTR(p, std::string{"t." + name}.c_str());
    p = vpi_get_str(vpiType, param_h);
    CHECK_RESULT_CSTR(p, "vpiParameter");
    vpi_type = vpi_get(vpiLocalParam, param_h);
    CHECK_RESULT_NZ(vpi_chk_error(&e));
    if (verbose && vpi_chk_error(&e)) {
        vpi_printf((PLI_BYTE8*)"    vpi_chk_error: %s\n", e.message);
    }

    // values
    if (verbose) vpi_printf((PLI_BYTE8*)"  Try writing value to %s ...\n", name.c_str());
    value.value.integer = exp_value;
    vpi_put_value(param_h, &value, NULL, vpiNoDelay);
    CHECK_RESULT_NZ(vpi_chk_error(&e));
    if (verbose && vpi_chk_error(&e)) {
        vpi_printf((PLI_BYTE8*)"    vpi_chk_error: %s\n", e.message);
    }

    if (verbose) vpi_printf((PLI_BYTE8*)"  Try reading value of %s ...\n", name.c_str());
    vpi_get_value(param_h, &value);
    CHECK_RESULT_NZ(!vpi_chk_error(&e));
    if (verbose && vpi_chk_error(&e)) {
        vpi_printf((PLI_BYTE8*)"    vpi_chk_error: %s\n", e.message);
    }
    if (verbose) {
        vpi_printf((PLI_BYTE8*)"    value of %s: %d\n", name.c_str(), value.value.integer);
    }
    CHECK_RESULT(value.value.integer, exp_value);

    return 0;
}

int check_param_str(std::string name, PLI_INT32 format, std::string exp_value, bool verbose) {
    int vpi_type;
    TestVpiHandle param_h;
    s_vpi_value value;
    value.format = format;
    value.value.integer = 0;
    s_vpi_error_info e;
    const char* p;

    vpi_printf((PLI_BYTE8*)"Check parameter %s vpi ...\n", name.c_str());
    param_h = vpi_handle_by_name((PLI_BYTE8*)TestSimulator::rooted(name.c_str()), NULL);
    CHECK_RESULT_NZ(param_h);
    vpi_type = vpi_get(vpiType, param_h);
    CHECK_RESULT(vpi_type, vpiParameter);
    if (verbose) {
        vpi_printf((PLI_BYTE8*)"  vpiType: %s (%d)\n", vpi_get_str(vpiType, param_h), vpi_type);
    }

    // attributes
    p = vpi_get_str(vpiName, param_h);
    CHECK_RESULT_CSTR(p, name.c_str());
    p = vpi_get_str(vpiFullName, param_h);
    CHECK_RESULT_CSTR(p, std::string{"t." + name}.c_str());
    p = vpi_get_str(vpiType, param_h);
    CHECK_RESULT_CSTR(p, "vpiParameter");
    vpi_type = vpi_get(vpiLocalParam, param_h);
    CHECK_RESULT_NZ(vpi_chk_error(&e));
    if (verbose && vpi_chk_error(&e)) {
        vpi_printf((PLI_BYTE8*)"    vpi_chk_error: %s\n", e.message);
    }

    // values
    if (verbose) vpi_printf((PLI_BYTE8*)"  Try writing value to %s ...\n", name.c_str());
    value.value.str = (PLI_BYTE8*)exp_value.c_str();
    vpi_put_value(param_h, &value, NULL, vpiNoDelay);
    CHECK_RESULT_NZ(vpi_chk_error(&e));
    if (verbose && vpi_chk_error(&e)) {
        vpi_printf((PLI_BYTE8*)"    vpi_chk_error: %s\n", e.message);
    }

    if (verbose) vpi_printf((PLI_BYTE8*)"  Try reading value of %s ...\n", name.c_str());
    vpi_get_value(param_h, &value);
    CHECK_RESULT_NZ(!vpi_chk_error(&e));
    if (verbose && vpi_chk_error(&e)) {
        vpi_printf((PLI_BYTE8*)"    vpi_chk_error: %s\n", e.message);
    }
    if (verbose) {
        vpi_printf((PLI_BYTE8*)"    value of %s: %s\n", name.c_str(), value.value.str);
    }
    CHECK_RESULT_CSTR(value.value.str, exp_value.c_str());

    return 0;
}

int _mon_check_param() {
    int status = 0;
#ifdef TEST_VERBOSE
    bool verbose = true;
#else
    bool verbose = false;
#endif

    status += check_param_int("WIDTH", vpiIntVal, 32, verbose);
    status += check_param_int("DEPTH", vpiIntVal, 16, verbose);
    status += check_param_str("PARAM_LONG", vpiHexStrVal, "fedcba9876543210", verbose);
    status += check_param_str("PARAM_STR", vpiStringVal, "'some string value'", verbose);
    return status;
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
    if (int status = _mon_check_param()) return status;
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

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    // we're going to be checking for these errors do don't crash out
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
        VerilatedVpi::callValueCbs();
        topp->clk = !topp->clk;
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
