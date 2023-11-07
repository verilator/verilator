// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2023 by Wilson Snyder and Marlon James. This program is free software; you can
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

#include "Vt_vpi_escape.h"
#include "Vt_vpi_escape__Dpi.h"
#include "svdpi.h"

#endif

#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;
unsigned int main_time = 0;

//======================================================================

// We cannot replace those with VL_STRINGIFY, not available when PLI is build
#define STRINGIFY(x) STRINGIFY2(x)
#define STRINGIFY2(x) #x

const char* _sim_top() {
    if (TestSimulator::is_verilator() || TestSimulator::is_icarus()) {
        return "\\t.has.dots ";
    } else {
        return "top.\\t.has.dots ";
    }
}

const char* _my_rooted(const char* obj) {
    static std::string buf;
    std::ostringstream os;
    os << _sim_top();
    if (*obj) os << "." << obj;
    buf = os.str();
    return buf.c_str();
}

#define MY_VPI_HANDLE(signal) vpi_handle_by_name(const_cast<PLI_BYTE8*>(_my_rooted(signal)), NULL);

int _mon_check_var() {
#ifdef TEST_VERBOSE
    printf("-mon_check_var()\n");
#endif
    TestVpiHandle vh1 = vpi_handle_by_name(const_cast<PLI_BYTE8*>(_sim_top()), NULL);
    TEST_CHECK_NZ(vh1);

    TestVpiHandle vh2 = MY_VPI_HANDLE("\\check;alias ");
    TEST_CHECK_NZ(vh2);

    // scope attributes
    const char* p;
    p = vpi_get_str(vpiName, vh1);
    TEST_CHECK_CSTR(p, "\\t.has.dots ");
    p = vpi_get_str(vpiFullName, vh1);
    TEST_CHECK_CSTR(p, _sim_top());
    p = vpi_get_str(vpiType, vh1);
    TEST_CHECK_CSTR(p, "vpiModule");

    TestVpiHandle vh3 = vpi_handle_by_name(const_cast<PLI_BYTE8*>("escaped_normal"), vh1);
    TEST_CHECK_NZ(vh3);

    // onebit attributes
    PLI_INT32 d;
    d = vpi_get(vpiType, vh3);
    if (TestSimulator::is_verilator()) {
        TEST_CHECK_EQ(d, vpiReg);
    } else {
        TEST_CHECK_EQ(d, vpiNet);
    }
    if (TestSimulator::has_get_scalar()) {
        d = vpi_get(vpiVector, vh3);
        TEST_CHECK_EQ(d, 0);
    }

    p = vpi_get_str(vpiName, vh3);
    TEST_CHECK_CSTR(p, "escaped_normal");
    p = vpi_get_str(vpiFullName, vh3);
    // Toplevel port returns TOP.xxxxx
    TEST_CHECK_CSTR(p, "TOP.escaped_normal");
    p = vpi_get_str(vpiType, vh3);
    if (TestSimulator::is_verilator()) {
        TEST_CHECK_CSTR(p, "vpiReg");
    } else {
        TEST_CHECK_CSTR(p, "vpiNet");
    }

    TestVpiHandle vh4 = MY_VPI_HANDLE("\\x.y ");
    TEST_CHECK_NZ(vh4);

    // Test that the toplevel TOP.xxxxx search is skipped
    // when the path to the scope has more than one level.
    TestVpiHandle vh5 = MY_VPI_HANDLE("\\mod.with_dot .\\b.c ");
    TEST_CHECK_NZ(vh5);
    p = vpi_get_str(vpiFullName, vh5);
    TEST_CHECK_CSTR(p, "\\t.has.dots .\\mod.with_dot .\\b.c ");

    return errors;
}

int _mon_check_iter() {
#ifdef TEST_VERBOSE
    printf("-mon_check_iter()\n");
#endif
    const char* p;

    TestVpiHandle vh2 = MY_VPI_HANDLE("\\mod.with_dot ");
    TEST_CHECK_NZ(vh2);
    p = vpi_get_str(vpiName, vh2);
    TEST_CHECK_CSTR(p, "\\mod.with_dot ");
    if (TestSimulator::is_verilator()) {
        p = vpi_get_str(vpiDefName, vh2);
        TEST_CHECK_CSTR(p, "<null>");  // Unsupported
    }

    TestVpiHandle vh10 = vpi_iterate(vpiReg, vh2);
    TEST_CHECK_NZ(vh10);
    TEST_CHECK_EQ(vpi_get(vpiType, vh10), vpiIterator);

    {
        TestVpiHandle vh11 = vpi_scan(vh10);
        TEST_CHECK_NZ(vh11);
        p = vpi_get_str(vpiFullName, vh11);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", p);
#endif
        TEST_CHECK_CSTR(p, _my_rooted("\\mod.with_dot .\\b.c "));
    }
    {
        TestVpiHandle vh12 = vpi_scan(vh10);
        TEST_CHECK_NZ(vh12);
        p = vpi_get_str(vpiFullName, vh12);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", p);
#endif
        TEST_CHECK_CSTR(p, _my_rooted("\\mod.with_dot .cyc"));
    }
    {
        TestVpiHandle vh13 = vpi_scan(vh10);
        TEST_CHECK_NZ(vh13);
        p = vpi_get_str(vpiFullName, vh13);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", p);
#endif
        TEST_CHECK_CSTR(p, _my_rooted("\\mod.with_dot .subsig1"));
    }
    {
        TestVpiHandle vh14 = vpi_scan(vh10);
        TEST_CHECK_NZ(vh14);
        p = vpi_get_str(vpiFullName, vh14);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", p);
#endif
        TEST_CHECK_CSTR(p, _my_rooted("\\mod.with_dot .subsig2"));
    }
    {
        TestVpiHandle vh15 = vpi_scan(vh10);
        vh10.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        TEST_CHECK_EQ(vh15, 0);
    }
    return errors;
}

int _mon_check_ports() {
#ifdef TEST_VERBOSE
    printf("-mon_check_ports()\n");
#endif
    // test writing to input port
    TestVpiHandle vh1 = MY_VPI_HANDLE("a");
    TEST_CHECK_NZ(vh1);

    PLI_INT32 d;
    d = vpi_get(vpiType, vh1);
    if (TestSimulator::is_verilator()) {
        TEST_CHECK_EQ(d, vpiReg);
    } else {
        TEST_CHECK_EQ(d, vpiNet);
    }

    const char* portFullName;
    if (TestSimulator::is_verilator()) {
        portFullName = "TOP.a";
    } else {
        portFullName = "t.a";
    }

    const char* name = vpi_get_str(vpiFullName, vh1);
    TEST_CHECK_EQ(strcmp(name, portFullName), 0);
    std::string handleName1 = name;

    s_vpi_value v;
    v.format = vpiIntVal;
    vpi_get_value(vh1, &v);
    TEST_CHECK_EQ(v.value.integer, 0);

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    v.value.integer = 2;
    vpi_put_value(vh1, &v, &t, vpiNoDelay);
    v.value.integer = 100;
    vpi_get_value(vh1, &v);
    TEST_CHECK_EQ(v.value.integer, 2);

    // get handle of toplevel module
    TestVpiHandle vht = MY_VPI_HANDLE("");
    TEST_CHECK_NZ(vht);

    d = vpi_get(vpiType, vht);
    TEST_CHECK_EQ(d, vpiModule);

    TestVpiHandle vhi = vpi_iterate(vpiReg, vht);
    TEST_CHECK_NZ(vhi);

    TestVpiHandle vh11;
    std::string handleName2;
    while ((vh11 = vpi_scan(vhi))) {
        const char* fn = vpi_get_str(vpiFullName, vh11);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", fn);
#endif
        if (0 == strcmp(fn, portFullName)) {
            handleName2 = fn;
            break;
        }
    }
    TEST_CHECK_NZ(vh11);  // If get zero we never found the variable
    vhi.release();
    TEST_CHECK_EQ(vpi_get(vpiType, vh11), vpiReg);

    TEST_CHECK_EQ(handleName1, handleName2);

    TestVpiHandle vh2 = MY_VPI_HANDLE("\\b.c ");
    TEST_CHECK_NZ(vh2);

    if (TestSimulator::is_verilator()) {
        portFullName = "TOP.\\b.c ";
    } else {
        portFullName = "t.\\b.c ";
    }

    name = vpi_get_str(vpiFullName, vh2);
    TEST_CHECK_EQ(strcmp(name, portFullName), 0);
    handleName1 = name;

    v.format = vpiIntVal;
    vpi_get_value(vh2, &v);
    TEST_CHECK_EQ(v.value.integer, 0);

    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    v.value.integer = 1;
    vpi_put_value(vh2, &v, &t, vpiNoDelay);
    v.value.integer = 0;
    vpi_get_value(vh2, &v);
    TEST_CHECK_EQ(v.value.integer, 1);

    vhi = vpi_iterate(vpiReg, vht);
    TEST_CHECK_NZ(vhi);

    while ((vh11 = vpi_scan(vhi))) {
        const char* fn = vpi_get_str(vpiFullName, vh11);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", fn);
#endif
        if (0 == strcmp(fn, portFullName)) {
            handleName2 = fn;
            break;
        }
    }
    TEST_CHECK_NZ(vh11);  // If get zero we never found the variable
    vhi.release();
    TEST_CHECK_EQ(vpi_get(vpiType, vh11), vpiReg);

    TEST_CHECK_EQ(handleName1, handleName2);

    return errors;
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
#ifdef TEST_VERBOSE
    printf("-mon_check()\n");
#endif

    if (int status = _mon_check_var()) return status;
    if (int status = _mon_check_iter()) return status;
    if (int status = _mon_check_ports()) return status;
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
        topp->eval();
        VerilatedVpi::callValueCbs();
        topp->clk = !topp->clk;
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(main_time);
#endif
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    return 0;
}

#endif
