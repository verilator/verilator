// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2010-2011 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"
#ifdef IS_VPI

#include "sv_vpi_user.h"

#else

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#ifdef T_VPI_VAR2
#include "Vt_vpi_var2.h"
#include "Vt_vpi_var2__Dpi.h"
#elif defined(T_VPI_VAR3)
#include "Vt_vpi_var3.h"
#include "Vt_vpi_var3__Dpi.h"
#else
#include "Vt_vpi_var.h"
#include "Vt_vpi_var__Dpi.h"
#endif

#include "svdpi.h"

#endif

#ifdef VERILATOR
#include "verilated.h"
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

#define TEST_MSG \
    if (0) printf

unsigned int main_time = 0;
unsigned int callback_count = 0;
unsigned int callback_count_half = 0;
unsigned int callback_count_quad = 0;
unsigned int callback_count_strs = 0;
unsigned int callback_count_strs_max = 500;

//======================================================================

// We cannot replace those with VL_STRINGIFY, not available when PLI is build
#define STRINGIFY(x) STRINGIFY2(x)
#define STRINGIFY2(x) #x

int _mon_check_mcd() {
    PLI_INT32 status;

    PLI_UINT32 mcd;
    PLI_BYTE8* filename = (PLI_BYTE8*)(STRINGIFY(TEST_OBJ_DIR) "/mcd_open.tmp");
    mcd = vpi_mcd_open(filename);
    CHECK_RESULT_NZ(mcd);

    {  // Check it got written
        FILE* fp = fopen(filename, "r");
        CHECK_RESULT_NZ(fp);
        fclose(fp);
    }

    status = vpi_mcd_printf(mcd, (PLI_BYTE8*)"hello %s", "vpi_mcd_printf");
    CHECK_RESULT(status, std::strlen("hello vpi_mcd_printf"));

    status = vpi_mcd_printf(0, (PLI_BYTE8*)"empty");
    CHECK_RESULT(status, 0);

    status = vpi_mcd_flush(mcd);
    CHECK_RESULT(status, 0);

    status = vpi_mcd_flush(0);
    CHECK_RESULT(status, 1);

    status = vpi_mcd_close(mcd);
    // Icarus says 'error' on ones we're not using, so check only used ones return 0.
    CHECK_RESULT(status & mcd, 0);

    status = vpi_flush();
    CHECK_RESULT(status, 0);

    return 0;
}

int _mon_check_callbacks_error(p_cb_data cb_data) {
    vpi_printf((PLI_BYTE8*)"%%Error: callback should not be executed\n");
    return 1;
}

int _mon_check_callbacks() {
    t_cb_data cb_data;
    cb_data.reason = cbEndOfSimulation;
    cb_data.cb_rtn = _mon_check_callbacks_error;
    cb_data.user_data = 0;
    cb_data.value = NULL;
    cb_data.time = NULL;

    TestVpiHandle vh = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh);

    PLI_INT32 status = vpi_remove_cb(vh);
    vh.freed();
    CHECK_RESULT_NZ(status);

    return 0;
}

int _value_callback(p_cb_data cb_data) {
    if (verbose) vpi_printf(const_cast<char*>("     _value_callback:\n"));
    if (TestSimulator::is_verilator()) {
        // this check only makes sense in Verilator
        CHECK_RESULT(cb_data->value->value.integer + 10, main_time);
    }
    callback_count++;
    return 0;
}

int _value_callback_half(p_cb_data cb_data) {
    if (TestSimulator::is_verilator()) {
        // this check only makes sense in Verilator
        CHECK_RESULT(cb_data->value->value.integer * 2 + 10, main_time);
    }
    callback_count_half++;
    return 0;
}

int _value_callback_quad(p_cb_data cb_data) {
    for (int index = 0; index < 2; index++) {
        CHECK_RESULT_HEX(cb_data->value->value.vector[1].aval,
                         (unsigned long)((index == 2) ? 0x1c77bb9bUL : 0x12819213UL));
        CHECK_RESULT_HEX(cb_data->value->value.vector[0].aval,
                         (unsigned long)((index == 2) ? 0x3784ea09UL : 0xabd31a1cUL));
    }
    callback_count_quad++;
    return 0;
}

int _value_callback_never(p_cb_data cb_data) {
    printf("%%Error: callback should never be called\n");
    exit(-1);
    return 0;
}

int _mon_check_value_callbacks() {
    s_vpi_value v;
    v.format = vpiIntVal;

    t_cb_data cb_data;
    cb_data.reason = cbValueChange;
    cb_data.time = NULL;

    {
        TestVpiHandle vh1 = VPI_HANDLE("count");
        CHECK_RESULT_NZ(vh1);

        vpi_get_value(vh1, &v);
        cb_data.value = &v;
        cb_data.obj = vh1;
        cb_data.cb_rtn = _value_callback;

        if (verbose) vpi_printf(const_cast<char*>("     vpi_register_cb(_value_callback):\n"));
        TestVpiHandle callback_h = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(callback_h);
    }
    {
        TestVpiHandle vh1 = VPI_HANDLE("half_count");
        CHECK_RESULT_NZ(vh1);

        cb_data.obj = vh1;
        cb_data.cb_rtn = _value_callback_half;

        TestVpiHandle callback_h = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(callback_h);
    }
    {
        TestVpiHandle vh1 = VPI_HANDLE("quads");
        CHECK_RESULT_NZ(vh1);

        v.format = vpiVectorVal;
        cb_data.obj = vh1;
        cb_data.cb_rtn = _value_callback_quad;

        TestVpiHandle callback_h = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(callback_h);
    }
    {
        TestVpiHandle vh1 = VPI_HANDLE("quads");
        CHECK_RESULT_NZ(vh1);
        TestVpiHandle vh2 = vpi_handle_by_index(vh1, 2);
        CHECK_RESULT_NZ(vh2);

        cb_data.obj = vh2;
        cb_data.cb_rtn = _value_callback_quad;

        TestVpiHandle callback_h = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(callback_h);
    }
    {
        TestVpiHandle vh1 = VPI_HANDLE("some_mem");
        CHECK_RESULT_NZ(vh1);
        TestVpiHandle vh2 = vpi_handle_by_index(vh1, 3);
        CHECK_RESULT_NZ(vh2);

        cb_data.obj = vh2;
        cb_data.cb_rtn = _value_callback_never;

        TestVpiHandle callback_h = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(callback_h);
    }
    return 0;
}

int _mon_check_big() {
#ifdef VERILATOR
    s_vpi_value v;
    v.format = vpiVectorVal;

    TestVpiHandle h = VPI_HANDLE("big");
    CHECK_RESULT_NZ(h);

    Verilated::fatalOnVpiError(false);
    vpi_get_value(h, &v);
    Verilated::fatalOnVpiError(true);
    s_vpi_error_info info;
    CHECK_RESULT_Z(vpi_chk_error(&info));

    v.format = vpiStringVal;
    vpi_get_value(h, &v);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    CHECK_RESULT_CSTR_STRIP(v.value.str, "some text");
#endif

    return 0;
}

int _mon_check_var() {
    TestVpiHandle vh1 = VPI_HANDLE("onebit");
    CHECK_RESULT_NZ(vh1);

    TestVpiHandle vh2 = vpi_handle_by_name((PLI_BYTE8*)TestSimulator::top(), NULL);
    CHECK_RESULT_NZ(vh2);

    // scope attributes
    const char* p;
    p = vpi_get_str(vpiName, vh2);
    CHECK_RESULT_CSTR(p, "t");
    p = vpi_get_str(vpiFullName, vh2);
    CHECK_RESULT_CSTR(p, TestSimulator::top());
    p = vpi_get_str(vpiType, vh2);
    CHECK_RESULT_CSTR(p, "vpiModule");

    TestVpiHandle vh3 = vpi_handle_by_name((PLI_BYTE8*)"onebit", vh2);
    CHECK_RESULT_NZ(vh3);

#ifdef T_VPI_VAR2
    // test scoped attributes
    TestVpiHandle vh_invisible1 = vpi_handle_by_name((PLI_BYTE8*)"invisible1", vh2);
    CHECK_RESULT_Z(vh_invisible1);

    TestVpiHandle vh_invisible2 = vpi_handle_by_name((PLI_BYTE8*)"invisible2", vh2);
    CHECK_RESULT_Z(vh_invisible2);

    TestVpiHandle vh_visibleParam1 = vpi_handle_by_name((PLI_BYTE8*)"visibleParam1", vh2);
    CHECK_RESULT_NZ(vh_visibleParam1);

    TestVpiHandle vh_invisibleParam1 = vpi_handle_by_name((PLI_BYTE8*)"invisibleParam1", vh2);
    CHECK_RESULT_Z(vh_invisibleParam1);

    TestVpiHandle vh_visibleParam2 = vpi_handle_by_name((PLI_BYTE8*)"visibleParam2", vh2);
    CHECK_RESULT_NZ(vh_visibleParam2);

#endif

    // onebit attributes
    PLI_INT32 d;
    d = vpi_get(vpiType, vh3);
    CHECK_RESULT(d, vpiReg);
    if (TestSimulator::has_get_scalar()) {
        d = vpi_get(vpiVector, vh3);
        CHECK_RESULT(d, 0);
    }

    p = vpi_get_str(vpiName, vh3);
    CHECK_RESULT_CSTR(p, "onebit");
    p = vpi_get_str(vpiFullName, vh3);
    CHECK_RESULT_CSTR(p, TestSimulator::rooted("onebit"));
    p = vpi_get_str(vpiType, vh3);
    CHECK_RESULT_CSTR(p, "vpiReg");

    // array attributes
    TestVpiHandle vh4 = VPI_HANDLE("fourthreetwoone");
    CHECK_RESULT_NZ(vh4);
    if (TestSimulator::has_get_scalar()) {
        d = vpi_get(vpiVector, vh4);
        CHECK_RESULT(d, 1);
        p = vpi_get_str(vpiType, vh4);
        CHECK_RESULT_CSTR(p, "vpiRegArray");
    }

    t_vpi_value tmpValue;
    tmpValue.format = vpiIntVal;
    {
        TestVpiHandle vh10 = vpi_handle(vpiLeftRange, vh4);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 4);
        CHECK_RESULT(vpi_get(vpiType, vh10), vpiConstant);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }
    {
        TestVpiHandle vh10 = vpi_handle(vpiRightRange, vh4);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 3);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }
    {
        TestVpiHandle vh10 = vpi_iterate(vpiReg, vh4);
        CHECK_RESULT_NZ(vh10);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiIterator");
        TestVpiHandle vh11 = vpi_scan(vh10);
        CHECK_RESULT_NZ(vh11);
        p = vpi_get_str(vpiType, vh11);
        CHECK_RESULT_CSTR(p, "vpiReg");
        TestVpiHandle vh12 = vpi_handle(vpiLeftRange, vh11);
        CHECK_RESULT_NZ(vh12);
        vpi_get_value(vh12, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 2);
        p = vpi_get_str(vpiType, vh12);
        CHECK_RESULT_CSTR(p, "vpiConstant");
        TestVpiHandle vh13 = vpi_handle(vpiRightRange, vh11);
        CHECK_RESULT_NZ(vh13);
        vpi_get_value(vh13, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 1);
        p = vpi_get_str(vpiType, vh13);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }

    TestVpiHandle vh5 = VPI_HANDLE("quads");
    CHECK_RESULT_NZ(vh5);
    {
        TestVpiHandle vh10 = vpi_handle(vpiLeftRange, vh5);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 2);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }
    {
        TestVpiHandle vh10 = vpi_handle(vpiRightRange, vh5);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 3);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }
    TestVpiHandle vh6 = vpi_handle_by_index(vh5, 2);
    CHECK_RESULT_NZ(vh6);
    {
        TestVpiHandle vh10 = vpi_handle(vpiLeftRange, vh6);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 0);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }
    {
        TestVpiHandle vh10 = vpi_handle(vpiRightRange, vh6);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 61);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiConstant");
    }

    // C++ keyword collision
    {
        TestVpiHandle vh10 = VPI_HANDLE("nullptr");
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &tmpValue);
        CHECK_RESULT(tmpValue.value.integer, 123);
        p = vpi_get_str(vpiType, vh10);
        CHECK_RESULT_CSTR(p, "vpiParameter");
    }

    // test properties on bad handle
    {
        TestVpiHandle vh999 = VPI_HANDLE("nonexistent");
        CHECK_RESULT_Z(vh999);
        d = vpi_get(vpiType, vh999);
        CHECK_RESULT(d, vpiUndefined);
        d = vpi_get(vpiSigned, vh999);
        CHECK_RESULT(d, vpiUndefined);
        d = vpi_get(vpiSize, vh999);
        CHECK_RESULT(d, vpiUndefined);
    }

    // other unsigned types
    {
        TestVpiHandle vh999 = VPI_HANDLE("bit1");
        CHECK_RESULT_NZ(vh999);
        d = vpi_get(vpiType, vh999);
        CHECK_RESULT(d, vpiBitVar);  // Required by uvm_hdl_polling
        for (PLI_INT32 i : {vpi0, vpi1, vpiX, vpiZ}) {
            t_vpi_value value;
            value.format = vpiScalarVal;
            value.value.scalar = i;
            vpi_put_value(vh999, &value, NULL, vpiNoDelay);
            value.value.scalar = 9;
            vpi_get_value(vh999, &value);
#ifdef VERILATOR  // 2-state
            const PLI_INT32 expv = (i == vpi1) ? vpi1 : vpi0;
#else
            const PLI_INT32 expv = i;
#endif
            TEST_CHECK_EQ(value.value.scalar, expv);
        }
    }

    // other integer types
    tmpValue.format = vpiIntVal;
    constexpr struct {
        const char* name;
        PLI_INT32 exp_sz;
    } int_vars[] = {
        {"integer1", 32}, {"byte1", 8}, {"short1", 16}, {"int1", 32}, {"long1", 64},
    };
    for (const auto& s : int_vars) {
        TestVpiHandle vh101 = VPI_HANDLE(s.name);
        CHECK_RESULT_NZ(vh101);
        d = vpi_get(vpiType, vh101);
        CHECK_RESULT(d, vpiReg);
        auto sz = vpi_get(vpiSize, vh101);
        CHECK_RESULT(sz, s.exp_sz);
        auto sn = vpi_get(vpiSigned, vh101);
        CHECK_RESULT(sn, 1);
        vpi_get_value(vh101, &tmpValue);
        TEST_CHECK_EQ(tmpValue.value.integer, 123);
        p = vpi_get_str(vpiType, vh101);
        CHECK_RESULT_CSTR(p, "vpiReg");
    }

    // non-integer variables
    tmpValue.format = vpiRealVal;
    {
        TestVpiHandle vh101 = VPI_HANDLE("real1");
        CHECK_RESULT_NZ(vh101);
        d = vpi_get(vpiType, vh101);
        CHECK_RESULT(d, vpiRealVar);
        auto sn = vpi_get(vpiSigned, vh101);
        CHECK_RESULT(sn, 1);
        vpi_get_value(vh101, &tmpValue);
        TEST_CHECK_REAL_EQ(tmpValue.value.real, 1.0, 0.0005);
        p = vpi_get_str(vpiType, vh101);
        CHECK_RESULT_CSTR(p, "vpiRealVar");
    }

    // string variable
    tmpValue.format = vpiStringVal;
    {
        TestVpiHandle vh101 = VPI_HANDLE("str1");
        CHECK_RESULT_NZ(vh101);
        d = vpi_get(vpiType, vh101);
        CHECK_RESULT(d, vpiStringVar);
        auto sn = vpi_get(vpiSigned, vh101);
        CHECK_RESULT(sn, 0);
        vpi_get_value(vh101, &tmpValue);
        CHECK_RESULT_CSTR(tmpValue.value.str, "hello");
        p = vpi_get_str(vpiType, vh101);
        CHECK_RESULT_CSTR(p, "vpiStringVar");
    }

    return errors;
}

int _mon_check_rev() {
    t_vpi_value value;
    TestVpiHandle vh9 = VPI_HANDLE("rev");
    CHECK_RESULT_NZ(vh9);
    value.format = vpiIntVal;
    {
        TestVpiHandle vh10 = vpi_handle(vpiLeftRange, vh9);
        CHECK_RESULT_NZ(vh10);
        vpi_get_value(vh10, &value);
        TEST_CHECK_EQ(value.value.integer, 8);
        TestVpiHandle vh11 = vpi_handle(vpiRightRange, vh9);
        CHECK_RESULT_NZ(vh11);
        vpi_get_value(vh11, &value);
        TEST_CHECK_EQ(value.value.integer, 19);

        value.format = vpiVectorVal;
        vpi_get_value(vh9, &value);
        CHECK_RESULT(value.value.vector[0].aval, 0xabc);
    }
    return errors;
}

int _mon_check_varlist() {
    const char* p;

    TestVpiHandle vh2 = VPI_HANDLE("sub");
    CHECK_RESULT_NZ(vh2);
    p = vpi_get_str(vpiName, vh2);
    CHECK_RESULT_CSTR(p, "sub");
    if (TestSimulator::is_verilator()) {
        p = vpi_get_str(vpiDefName, vh2);
        CHECK_RESULT_CSTR(p, "sub");
    }

    TestVpiHandle vh10 = vpi_iterate(vpiReg, vh2);
    CHECK_RESULT_NZ(vh10);
    CHECK_RESULT(vpi_get(vpiType, vh10), vpiIterator);

    {
        TestVpiHandle vh11 = vpi_scan(vh10);
        CHECK_RESULT_NZ(vh11);
        p = vpi_get_str(vpiFullName, vh11);
        CHECK_RESULT_CSTR(p, TestSimulator::rooted("sub.subsig1"));
    }
    {
        TestVpiHandle vh12 = vpi_scan(vh10);
        CHECK_RESULT_NZ(vh12);
        p = vpi_get_str(vpiFullName, vh12);
        CHECK_RESULT_CSTR(p, TestSimulator::rooted("sub.subsig2"));
    }
    {
        TestVpiHandle vh13 = vpi_scan(vh10);
        vh10.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        CHECK_RESULT(vh13, 0);
    }
    return 0;
}

void touch_signal() {
    TestVpiHandle vh1 = VPI_HANDLE("count");
    TEST_CHECK_NZ(vh1);
    s_vpi_value v;
    v.format = vpiIntVal;
    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    v.value.integer = 0;
    vpi_put_value(vh1, &v, &t, vpiNoDelay);
}

int _mon_check_ports() {
#ifdef TEST_VERBOSE
    printf("-mon_check_ports()\n");
#endif
    // test writing to input port
    TestVpiHandle vh1 = VPI_HANDLE("a");
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
    TestVpiHandle vht = VPI_HANDLE("");
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

    return errors;
}

int _mon_check_getput() {
    TestVpiHandle vh2 = VPI_HANDLE("onebit");
    CHECK_RESULT_NZ(vh2);
    const char* p = vpi_get_str(vpiFullName, vh2);
    CHECK_RESULT_CSTR(p, "t.onebit");

    s_vpi_value v;
    v.format = vpiIntVal;
    vpi_get_value(vh2, &v);
    CHECK_RESULT(v.value.integer, 0);

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    v.value.integer = 0;
    vpi_put_value(vh2, &v, &t, vpiNoDelay);
    vpi_get_value(vh2, &v);
    CHECK_RESULT(v.value.integer, 0);

    v.value.integer = 1;
    vpi_put_value(vh2, &v, &t, vpiNoDelay);
    vpi_get_value(vh2, &v);
    CHECK_RESULT(v.value.integer, 1);

    // real
    TestVpiHandle vh3 = VPI_HANDLE("real1");
    CHECK_RESULT_NZ(vh3);
    v.format = vpiRealVal;
    vpi_get_value(vh3, &v);
    TEST_CHECK_REAL_EQ(v.value.real, 1.0, 0.0005);

    v.value.real = 123456.789;
    vpi_put_value(vh3, &v, &t, vpiNoDelay);
    v.value.real = 0.0f;
    vpi_get_value(vh3, &v);
    TEST_CHECK_REAL_EQ(v.value.real, 123456.789, 0.0005);

    // string
    TestVpiHandle vh4 = VPI_HANDLE("str1");
    CHECK_RESULT_NZ(vh4);
    v.format = vpiStringVal;
    vpi_get_value(vh4, &v);
    CHECK_RESULT_CSTR(v.value.str, "hello");

    v.value.str = const_cast<char*>("something a lot longer than hello");
    vpi_put_value(vh4, &v, &t, vpiNoDelay);
    v.value.str = 0;
    vpi_get_value(vh4, &v);
    TEST_CHECK_CSTR(v.value.str, "something a lot longer than hello");

    return errors;
}

int _mon_check_var_long_name() {
    TestVpiHandle vh2 = VPI_HANDLE(
        "LONGSTART_a_very_long_name_which_will_get_hashed_a_very_long_name_which_will_get_hashed_"
        "a_very_long_name_which_will_get_hashed_a_very_long_name_which_will_get_hashed_LONGEND");
    CHECK_RESULT_NZ(vh2);
    const char* p = vpi_get_str(vpiFullName, vh2);
    CHECK_RESULT_CSTR(p, "t.LONGSTART_a_very_long_name_which_will_get_hashed_a_very_long_name_"
                         "which_will_get_hashed_a_very_long_name_which_will_get_hashed_a_very_"
                         "long_name_which_will_get_hashed_LONGEND");
    return 0;
}

int _mon_check_getput_iter() {
    TestVpiHandle vh2 = VPI_HANDLE("sub");
    CHECK_RESULT_NZ(vh2);
    TestVpiHandle vh10 = vpi_iterate(vpiReg, vh2);
    CHECK_RESULT_NZ(vh10);
    CHECK_RESULT(vpi_get(vpiType, vh10), vpiIterator);

    TestVpiHandle vh11;
    while (1) {
        vh11 = vpi_scan(vh10);
        CHECK_RESULT_NZ(vh11);  // If get zero we never found the variable
        const char* p = vpi_get_str(vpiFullName, vh11);
#ifdef TEST_VERBOSE
        printf("       scanned %s\n", p);
#endif
        if (0 == strcmp(p, "t.sub.subsig1")) break;
    }
    CHECK_RESULT(vpi_get(vpiType, vh11), vpiReg);

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    s_vpi_value v;
    v.format = vpiIntVal;
    v.value.integer = 0;
    vpi_put_value(vh11, &v, &t, vpiNoDelay);
    vpi_get_value(vh11, &v);
    CHECK_RESULT(v.value.integer, 0);

    v.value.integer = 1;
    vpi_put_value(vh11, &v, &t, vpiNoDelay);
    vpi_get_value(vh11, &v);
    CHECK_RESULT(v.value.integer, 1);
    return 0;
}

int _mon_check_quad() {
    TestVpiHandle vh2 = VPI_HANDLE("quads");
    CHECK_RESULT_NZ(vh2);

    s_vpi_value v;
    t_vpi_vecval vv[2];
    bzero(&vv, sizeof(vv));

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;

    TestVpiHandle vhidx2 = vpi_handle_by_index(vh2, 2);
    CHECK_RESULT_NZ(vhidx2);
    TestVpiHandle vhidx3 = vpi_handle_by_index(vh2, 3);
    CHECK_RESULT_NZ(vhidx3);

    // Packed words should be indexable
    TestVpiHandle vhidx3idx0 = vpi_handle_by_index(vhidx3, 0);
    CHECK_RESULT_NZ(vhidx3idx0);
    TestVpiHandle vhidx2idx2 = vpi_handle_by_index(vhidx2, 2);
    CHECK_RESULT_NZ(vhidx2idx2);
    TestVpiHandle vhidx3idx3 = vpi_handle_by_index(vhidx3, 3);
    CHECK_RESULT_NZ(vhidx3idx3);
    TestVpiHandle vhidx2idx61 = vpi_handle_by_index(vhidx2, 61);
    CHECK_RESULT_NZ(vhidx2idx61);

    v.format = vpiVectorVal;
    v.value.vector = vv;
    v.value.vector[1].aval = 0x12819213UL;
    v.value.vector[0].aval = 0xabd31a1cUL;
    vpi_put_value(vhidx2, &v, &t, vpiNoDelay);

    v.format = vpiVectorVal;
    v.value.vector = vv;
    v.value.vector[1].aval = 0x1c77bb9bUL;
    v.value.vector[0].aval = 0x3784ea09UL;
    vpi_put_value(vhidx3, &v, &t, vpiNoDelay);

    vpi_get_value(vhidx2, &v);
    CHECK_RESULT(v.value.vector[1].aval, 0x12819213UL);
    CHECK_RESULT(v.value.vector[1].bval, 0);

    vpi_get_value(vhidx3, &v);
    CHECK_RESULT(v.value.vector[1].aval, 0x1c77bb9bUL);
    CHECK_RESULT(v.value.vector[1].bval, 0);

    return 0;
}

int _mon_check_delayed() {
    TestVpiHandle vh = VPI_HANDLE("delayed");
    CHECK_RESULT_NZ(vh);

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;

    s_vpi_value v;
    v.format = vpiIntVal;
    v.value.integer = 123;
    vpi_put_value(vh, &v, &t, vpiInertialDelay);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    vpi_get_value(vh, &v);
    CHECK_RESULT(v.value.integer, 0);

    TestVpiHandle vhMem = VPI_HANDLE("delayed_mem");
    CHECK_RESULT_NZ(vhMem);
    TestVpiHandle vhMemWord = vpi_handle_by_index(vhMem, 7);
    CHECK_RESULT_NZ(vhMemWord);
    v.value.integer = 456;
    vpi_put_value(vhMemWord, &v, &t, vpiInertialDelay);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));

    // test unsupported vpiInertialDelay cases
    // - should these also throw vpi errors?
    v.format = vpiStringVal;
    v.value.str = nullptr;
    vpi_put_value(vh, &v, &t, vpiInertialDelay);
    CHECK_RESULT_NZ(vpi_chk_error(nullptr));

    v.format = vpiVectorVal;
    v.value.vector = nullptr;
    vpi_put_value(vh, &v, &t, vpiInertialDelay);
    CHECK_RESULT_NZ(vpi_chk_error(nullptr));

    // This format throws an error now
#ifdef VERILATOR
    Verilated::fatalOnVpiError(false);
#endif
    v.format = vpiObjTypeVal;
    vpi_put_value(vh, &v, &t, vpiInertialDelay);
#ifdef VERILATOR
    Verilated::fatalOnVpiError(true);
#endif

    return 0;
}

int _mon_check_string() {
    static struct {
        const char* name;
        const char* initial;
        const char* value;
    } text_test_obs[] = {
        {"text_byte", "B", "xxA"},  // x's dropped
        {"text_half", "Hf", "xxT2"},  // x's dropped
        {"text_word", "Word", "Tree"},
        {"text_long", "Long64b", "44Four44"},
        {"text", "Verilog Test module", "lorem ipsum"},
    };

    for (int i = 0; i < 5; i++) {
        TestVpiHandle vh1 = VPI_HANDLE(text_test_obs[i].name);
        CHECK_RESULT_NZ(vh1);

        s_vpi_value v;
        s_vpi_time t = {vpiSimTime, 0, 0, 0.0};
        s_vpi_error_info e;

        v.format = vpiStringVal;
        vpi_get_value(vh1, &v);
        if (vpi_chk_error(&e)) printf("%%vpi_chk_error : %s\n", e.message);

        (void)vpi_chk_error(NULL);

        CHECK_RESULT_CSTR_STRIP(v.value.str, text_test_obs[i].initial);

        v.value.str = (PLI_BYTE8*)text_test_obs[i].value;
        vpi_put_value(vh1, &v, &t, vpiNoDelay);
    }

    return 0;
}

int _mon_check_putget_str(p_cb_data cb_data) {
    static TestVpiHandle cb;
    static struct {
        TestVpiHandle scope, sig, rfr, check, verbose;
        std::string str;
        int type;  // value type in .str
        union {
            PLI_INT32 integer;
            s_vpi_vecval vector[4];
        } value;  // reference
    } data[129];

    if (cb_data) {
        if (verbose) vpi_printf(const_cast<char*>("     _mon_check_putget_str callback:\n"));

        // this is the callback
        static unsigned int seed = 1;
        s_vpi_time t;
        t.type = vpiSimTime;
        t.high = 0;
        t.low = 0;
        for (int i = 2; i <= 6; i++) {
            static s_vpi_value v;
            int words = (i + 31) >> 5;
            TEST_MSG("========== %d ==========\n", i);
            if (callback_count_strs) {
                // check persistence
                if (data[i].type) {
                    v.format = data[i].type;
                } else {
                    static PLI_INT32 vals[]
                        = {vpiBinStrVal, vpiOctStrVal, vpiHexStrVal, vpiDecStrVal};
                    v.format = vals[rand_r(&seed) % ((words > 2) ? 3 : 4)];
                    TEST_MSG("new format %d\n", v.format);
                }
                vpi_get_value(data[i].sig, &v);
                TEST_MSG("%s\n", v.value.str);
                if (data[i].type) {
                    CHECK_RESULT_CSTR(v.value.str, data[i].str.c_str());
                } else {
                    data[i].type = v.format;
                    data[i].str = std::string{v.value.str};
                }
            }

            // check for corruption
            v.format = (words == 1) ? vpiIntVal : vpiVectorVal;
            vpi_get_value(data[i].sig, &v);
            if (v.format == vpiIntVal) {
                TEST_MSG("%08x %08x\n", v.value.integer, data[i].value.integer);
                CHECK_RESULT(v.value.integer, data[i].value.integer);
            } else {
                for (int k = 0; k < words; k++) {
                    TEST_MSG("%d %08x %08x\n", k, v.value.vector[k].aval,
                             data[i].value.vector[k].aval);
                    CHECK_RESULT_HEX(v.value.vector[k].aval, data[i].value.vector[k].aval);
                }
            }

            if (callback_count_strs & 7) {
                // put same value back - checking encoding/decoding equivalent
                v.format = data[i].type;
                v.value.str = (PLI_BYTE8*)(data[i].str.c_str());  // Can't reinterpret_cast
                vpi_put_value(data[i].sig, &v, &t, vpiNoDelay);
                v.format = vpiIntVal;
                v.value.integer = 1;
                // vpi_put_value(data[i].verbose, &v, &t, vpiNoDelay);
                vpi_put_value(data[i].check, &v, &t, vpiNoDelay);
            } else {
                // stick a new random value in
                unsigned int mask = ((i & 31) ? (1 << (i & 31)) : 0) - 1;
                if (words == 1) {
                    v.value.integer = rand_r(&seed);
                    data[i].value.integer = v.value.integer &= mask;
                    v.format = vpiIntVal;
                    TEST_MSG("new value %08x\n", data[i].value.integer);
                } else {
                    TEST_MSG("new value\n");
                    for (int j = 0; j < 4; j++) {
                        data[i].value.vector[j].aval = rand_r(&seed);
                        if (j == (words - 1)) data[i].value.vector[j].aval &= mask;
                        TEST_MSG(" %08x\n", data[i].value.vector[j].aval);
                    }
                    v.value.vector = data[i].value.vector;
                    v.format = vpiVectorVal;
                }
                vpi_put_value(data[i].sig, &v, &t, vpiNoDelay);
                vpi_put_value(data[i].rfr, &v, &t, vpiNoDelay);
            }
            if ((callback_count_strs & 1) == 0) data[i].type = 0;
        }
        if (++callback_count_strs == callback_count_strs_max) {
            int success = vpi_remove_cb(cb);
            cb.freed();
            CHECK_RESULT_NZ(success);
        };
    } else {
        // setup and install
        for (int i = 1; i <= 6; i++) {
            char buf[32];
            VL_SNPRINTF(buf, sizeof(buf), TestSimulator::rooted("arr[%d].arr"), i);
            CHECK_RESULT_NZ(data[i].scope = vpi_handle_by_name((PLI_BYTE8*)buf, NULL));
            CHECK_RESULT_NZ(data[i].sig = vpi_handle_by_name((PLI_BYTE8*)"sig", data[i].scope));
            CHECK_RESULT_NZ(data[i].rfr = vpi_handle_by_name((PLI_BYTE8*)"rfr", data[i].scope));
            CHECK_RESULT_NZ(data[i].check
                            = vpi_handle_by_name((PLI_BYTE8*)"check", data[i].scope));
            CHECK_RESULT_NZ(data[i].verbose
                            = vpi_handle_by_name((PLI_BYTE8*)"verbose", data[i].scope));
        }

        for (int i = 1; i <= 6; i++) {
            char buf[32];
            VL_SNPRINTF(buf, sizeof(buf), TestSimulator::rooted("subs[%d].subsub"), i);
            CHECK_RESULT_NZ(data[i].scope = vpi_handle_by_name((PLI_BYTE8*)buf, NULL));
        }

        static t_cb_data cb_data;
        static s_vpi_value v;
        TestVpiHandle count_h = VPI_HANDLE("count");

        cb_data.reason = cbValueChange;
        cb_data.cb_rtn = _mon_check_putget_str;  // this function
        cb_data.obj = count_h;
        cb_data.value = &v;
        cb_data.time = NULL;
        v.format = vpiIntVal;

        cb = vpi_register_cb(&cb_data);
        // It is legal to free the callback handle immediately if not otherwise needed
        CHECK_RESULT_NZ(cb);
    }
    return 0;
}

int _mon_check_vlog_info() {
    s_vpi_vlog_info vlog_info;
    PLI_INT32 rtn = vpi_get_vlog_info(&vlog_info);
    CHECK_RESULT(rtn, 1);
    CHECK_RESULT(vlog_info.argc, 4);
    CHECK_RESULT_CSTR(vlog_info.argv[1], "+PLUS");
    CHECK_RESULT_CSTR(vlog_info.argv[2], "+INT=1234");
    CHECK_RESULT_CSTR(vlog_info.argv[3], "+STRSTR");
    CHECK_RESULT_Z(vlog_info.argv[4]);
    if (TestSimulator::is_verilator()) {
        CHECK_RESULT_CSTR(vlog_info.product, "Verilator");
        CHECK_RESULT(std::strlen(vlog_info.version) > 0, 1);
    }
    return 0;
}

int _mon_check_multi_index() {
    s_vpi_value v;
    v.format = vpiIntVal;

    // vpi_handle_by_multi_index tests

    // Basic tests for vpi_handle_by_multi_index
    {
        // 1D unpacked array: quads[2:3] with 62-bit elements
        TestVpiHandle vh_1d_base = vpi_handle_by_name((PLI_BYTE8*)"t.quads", nullptr);
        CHECK_RESULT_NZ(vh_1d_base);
        PLI_INT32 idx_1d[1] = {2};
        TestVpiHandle vh_1d = vpi_handle_by_multi_index(vh_1d_base, 1, idx_1d);
        CHECK_RESULT_NZ(vh_1d);
        CHECK_RESULT(vpi_get(vpiType, vh_1d), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_1d), 62);

        // 2D unpacked array: mem_2d[3:0][7:0] with 8-bit elements
        TestVpiHandle vh_2d_base = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d", nullptr);
        CHECK_RESULT_NZ(vh_2d_base);
        PLI_INT32 idx_2d[2] = {1, 3};
        TestVpiHandle vh_2d = vpi_handle_by_multi_index(vh_2d_base, 2, idx_2d);
        CHECK_RESULT_NZ(vh_2d);
        CHECK_RESULT(vpi_get(vpiType, vh_2d), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_2d), 8);
        vpi_get_value(vh_2d, &v);
        CHECK_RESULT(v.value.integer, 11);  // 1*8 + 3

        // 3D unpacked array: mem_3d[0:1][1:0][0:1] with 96-bit elements
        TestVpiHandle vh_3d_base = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d", nullptr);
        CHECK_RESULT_NZ(vh_3d_base);
        PLI_INT32 idx_3d[3] = {1, 1, 1};
        TestVpiHandle vh_3d = vpi_handle_by_multi_index(vh_3d_base, 3, idx_3d);
        CHECK_RESULT_NZ(vh_3d);
        CHECK_RESULT(vpi_get(vpiType, vh_3d), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_3d), 96);
        vpi_get_value(vh_3d, &v);
        CHECK_RESULT(v.value.integer, 7);  // (1*4) + (1*2) + 1

        // 2D Packed array with negative indices: [8:-7] [3:-4] negative_multi_packed[0:-2]
        TestVpiHandle vh_neg_packed_base
            = vpi_handle_by_name((PLI_BYTE8*)"t.negative_multi_packed", nullptr);
        CHECK_RESULT_NZ(vh_neg_packed_base);
        PLI_INT32 idx_neg_packed[2] = {-1, -2};
        TestVpiHandle vh_neg_packed
            = vpi_handle_by_multi_index(vh_neg_packed_base, 2, idx_neg_packed);
        CHECK_RESULT_NZ(vh_neg_packed);
        CHECK_RESULT(vpi_get(vpiType, vh_neg_packed), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_neg_packed), 8);
        vpi_get_value(vh_neg_packed, &v);
        CHECK_RESULT(v.value.integer, 4);

        // Verify multi_index matches sequential vpi_handle_by_index
        TestVpiHandle vh_seq_base = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d", nullptr);
        CHECK_RESULT_NZ(vh_seq_base);
        TestVpiHandle vh_seq_1 = vpi_handle_by_index(vh_seq_base, 1);
        CHECK_RESULT_NZ(vh_seq_1);
        TestVpiHandle vh_seq_2 = vpi_handle_by_index(vh_seq_1, 3);
        CHECK_RESULT_NZ(vh_seq_2);
        vpi_get_value(vh_seq_2, &v);
        CHECK_RESULT(v.value.integer, 11);
    }

    // Error handling for vpi_handle_by_multi_index
    {
        // Null handle
        PLI_INT32 idx_null[1] = {0};
        TestVpiHandle vh_null_hdl = vpi_handle_by_multi_index(nullptr, 1, idx_null);
        CHECK_RESULT_Z(vh_null_hdl);

        // Null index array
        TestVpiHandle vh_base = vpi_handle_by_name((PLI_BYTE8*)"t.quads", nullptr);
        CHECK_RESULT_NZ(vh_base);
        TestVpiHandle vh_null_idx = vpi_handle_by_multi_index(vh_base, 1, nullptr);
        CHECK_RESULT_Z(vh_null_idx);

        // Zero num_index
        PLI_INT32 idx_zero[1] = {0};
        TestVpiHandle vh_zero = vpi_handle_by_multi_index(vh_base, 0, idx_zero);
        CHECK_RESULT_Z(vh_zero);

        // Negative num_index
        PLI_INT32 idx_neg[1] = {0};
        TestVpiHandle vh_neg = vpi_handle_by_multi_index(vh_base, -1, idx_neg);
        CHECK_RESULT_Z(vh_neg);
    }

    // Bound checking
    {
        // Out of bounds on 1D array (quads is [2:3])
        TestVpiHandle vh_1d = vpi_handle_by_name((PLI_BYTE8*)"t.quads", nullptr);
        CHECK_RESULT_NZ(vh_1d);
        PLI_INT32 idx_oob_1d[1] = {99};
        TestVpiHandle vh_oob_1d = vpi_handle_by_multi_index(vh_1d, 1, idx_oob_1d);
        CHECK_RESULT_Z(vh_oob_1d);

        // Out of bounds on 2D array (mem_2d[3:0][7:0])
        TestVpiHandle vh_2d = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d", nullptr);
        CHECK_RESULT_NZ(vh_2d);
        PLI_INT32 idx_oob_2d[2] = {0, 99};
        TestVpiHandle vh_oob_2d = vpi_handle_by_multi_index(vh_2d, 2, idx_oob_2d);
        CHECK_RESULT_Z(vh_oob_2d);
    }

    // Boundary: lowest and highest valid indices on 2D array
    {
        TestVpiHandle vh1 = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d", nullptr);
        CHECK_RESULT_NZ(vh1);
        PLI_INT32 lo[2] = {0, 0};
        TestVpiHandle vh2 = vpi_handle_by_multi_index(vh1, 2, lo);
        CHECK_RESULT_NZ(vh2);
        vpi_get_value(vh2, &v);
        CHECK_RESULT(v.value.integer, 0);
        PLI_INT32 hi[2] = {3, 7};
        TestVpiHandle vh3 = vpi_handle_by_multi_index(vh1, 2, hi);
        CHECK_RESULT_NZ(vh3);
        vpi_get_value(vh3, &v);
        CHECK_RESULT(v.value.integer, 31);  // 3*8 + 7
    }

    // Packed dimension indexing: mem_3d fully indexed gives 96-bit element (VLWide)
    {
        PLI_INT32 indices[3] = {0, 0, 0};
        TestVpiHandle vh_elem = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d", nullptr);
        CHECK_RESULT_NZ(vh_elem);
        TestVpiHandle vh_3d = vpi_handle_by_multi_index(vh_elem, 3, indices);
        CHECK_RESULT_NZ(vh_3d);
        // Bit selection within element
        TestVpiHandle vh_3d_bit0 = vpi_handle_by_index(vh_3d, 0);
        CHECK_RESULT_NZ(vh_3d_bit0);
        CHECK_RESULT(vpi_get(vpiSize, vh_3d_bit0), 1);
        // Out of range bit
        TestVpiHandle vh_3d_oob = vpi_handle_by_index(vh_3d, 96);
        CHECK_RESULT_Z(vh_3d_oob);
    }

    // vpi_handle_by_name indexing tests

    {
        // Escaped identifier with literal brackets in the name
        TestVpiHandle vh_esc
            = vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped_with_brackets[3] ", nullptr);
        CHECK_RESULT_NZ(vh_esc);
        CHECK_RESULT(vpi_get(vpiType, vh_esc), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_esc), 8);
        vpi_get_value(vh_esc, &v);
        CHECK_RESULT(v.value.integer, 0x5a);

        // Escaped identifier with whitespace and trailing part-select
        // 0x5a = 0b01011010, [7:4] = 0b0101 = 5
        TestVpiHandle vh_esc_ps
            = vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped_with_brackets[3] [7:4]", nullptr);
        CHECK_RESULT_NZ(vh_esc_ps);
        CHECK_RESULT(vpi_get(vpiType, vh_esc_ps), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_esc_ps), 4);
        vpi_get_value(vh_esc_ps, &v);
        CHECK_RESULT(v.value.integer, 0x5);

        // Escaped identifier with multiple whitespaces and trailing part-select
        // 0x5a = 0b01011010, [3:0] = 0b1010 = 0xa
        TestVpiHandle vh_esc_ps_multispace
            = vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped_with_brackets[3]  [3:0]", nullptr);
        CHECK_RESULT_NZ(vh_esc_ps_multispace);
        CHECK_RESULT(vpi_get(vpiType, vh_esc_ps_multispace), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_esc_ps_multispace), 4);
        vpi_get_value(vh_esc_ps_multispace, &v);
        CHECK_RESULT(v.value.integer, 0xa);

        // Escaped instance name (with brackets as part of identifier) accessed through hierarchy
        TestVpiHandle vh_escaped_inst_sig
            = vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped.inst[0] .sig", nullptr);
        CHECK_RESULT_NZ(vh_escaped_inst_sig);
        CHECK_RESULT(vpi_get(vpiType, vh_escaped_inst_sig), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_escaped_inst_sig), 8);

        // Escaped instance name with part-select
        TestVpiHandle vh_escaped_inst_sig_ps
            = vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped.inst[0] .sig[3:0]", nullptr);
        CHECK_RESULT_NZ(vh_escaped_inst_sig_ps);
        CHECK_RESULT(vpi_get(vpiType, vh_escaped_inst_sig_ps), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_escaped_inst_sig_ps), 4);

        // Two escaped identifiers in the path: escaped instance + escaped signal name
        TestVpiHandle vh_two_escapes
            = vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped.inst[0] .\\escaped_sig[1] ", nullptr);
        CHECK_RESULT_NZ(vh_two_escapes);
        CHECK_RESULT(vpi_get(vpiType, vh_two_escapes), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_two_escapes), 8);

        // Two escaped identifiers with part-select and consecutive spaces
        TestVpiHandle vh_two_escapes_ps = vpi_handle_by_name(
            (PLI_BYTE8*)"t.\\escaped.inst[0]    .\\escaped_sig[1]       [3:0]", nullptr);
        CHECK_RESULT_NZ(vh_two_escapes_ps);
        CHECK_RESULT(vpi_get(vpiType, vh_two_escapes_ps), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_two_escapes_ps), 4);
    }

    // vpi_handle_by_name with generated signal
    {
        // Retrieve signal
        TestVpiHandle vh_generated = vpi_handle_by_name((PLI_BYTE8*)"t.gen[0].gen_sig", NULL);
        CHECK_RESULT_NZ(vh_generated);
        CHECK_RESULT(vpi_get(vpiType, vh_generated), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_generated), 8);
        vpi_get_value(vh_generated, &v);
        CHECK_RESULT(v.value.integer, 0xAB);

        // Single bit indexing
        TestVpiHandle vh_generated_bit
            = vpi_handle_by_name((PLI_BYTE8*)"t.gen[0].gen_sig[3]", NULL);
        CHECK_RESULT_NZ(vh_generated_bit);
        CHECK_RESULT(vpi_get(vpiType, vh_generated_bit), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_generated_bit), 1);
        vpi_get_value(vh_generated_bit, &v);
        CHECK_RESULT(v.value.integer, 1);

        // Generated scope
        TestVpiHandle vh_generated_scope = vpi_handle_by_name((PLI_BYTE8*)"t.subs[1]", NULL);
        CHECK_RESULT_NZ(vh_generated_scope);
        CHECK_RESULT(vpi_get(vpiType, vh_generated_scope), vpiGenScope);

        // Signal in generated instance
        TestVpiHandle vh_generated_inst
            = vpi_handle_by_name((PLI_BYTE8*)"t.subs[1].subsub.subsig1", NULL);
        CHECK_RESULT_NZ(vh_generated_inst);
        CHECK_RESULT(vpi_get(vpiType, vh_generated_inst), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_generated_inst), 1);
    }

    // vpi_handle_by_name with array indexing
    {
        TestVpiHandle vh_1d = vpi_handle_by_name((PLI_BYTE8*)"t.quads[2]", nullptr);
        CHECK_RESULT_NZ(vh_1d);
        CHECK_RESULT(vpi_get(vpiType, vh_1d), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_1d), 62);

        TestVpiHandle vh_2d = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[1][3]", nullptr);
        CHECK_RESULT_NZ(vh_2d);
        CHECK_RESULT(vpi_get(vpiSize, vh_2d), 8);
        vpi_get_value(vh_2d, &v);
        CHECK_RESULT(v.value.integer, 11);

        TestVpiHandle vh_3d = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1]", nullptr);
        CHECK_RESULT_NZ(vh_3d);
        CHECK_RESULT(vpi_get(vpiSize, vh_3d), 96);
        vpi_get_value(vh_3d, &v);
        CHECK_RESULT(v.value.integer, 7);

        // Index into single bit with negative index
        TestVpiHandle vh_neg_bit
            = vpi_handle_by_name((PLI_BYTE8*)"t.negative_multi_packed[-1][-2][-2]", nullptr);
        CHECK_RESULT_NZ(vh_neg_bit);
        CHECK_RESULT(vpi_get(vpiSize, vh_neg_bit), 1);
        vpi_get_value(vh_neg_bit, &v);
        // Element [-1][-2] is 8'h4; elements are indexed as [3:-4], so bit -2 is 1
        CHECK_RESULT(v.value.integer, 1);
    }

    // Packed dimension indexing: quads[2] bit selection
    {
        TestVpiHandle vh_arr = vpi_handle_by_name((PLI_BYTE8*)"t.quads[2]", nullptr);
        CHECK_RESULT_NZ(vh_arr);
        TestVpiHandle vh_bit0 = vpi_handle_by_index(vh_arr, 0);
        CHECK_RESULT_NZ(vh_bit0);
        CHECK_RESULT(vpi_get(vpiType, vh_bit0), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_bit0), 1);
        // Try to index into a single bit
        TestVpiHandle vh_invalid = vpi_handle_by_index(vh_bit0, 0);
        CHECK_RESULT_Z(vh_invalid);

        TestVpiHandle vh_bit32 = vpi_handle_by_index(vh_arr, 32);
        CHECK_RESULT_NZ(vh_bit32);
        CHECK_RESULT(vpi_get(vpiSize, vh_bit32), 1);
        // Out of range bit should fail
        TestVpiHandle vh_oob = vpi_handle_by_index(vh_arr, 100);
        CHECK_RESULT_Z(vh_oob);
    }

    // Multiple packed dimensions: multi_packed is [0:15][0:3][7:0] multi_packed[2:0]
    {
        TestVpiHandle vh1 = vpi_handle_by_name((PLI_BYTE8*)"t.multi_packed[1]", nullptr);
        CHECK_RESULT_NZ(vh1);
        CHECK_RESULT(vpi_get(vpiSize, vh1), 512);  // 16*8*4

        // Index into first packed dim
        TestVpiHandle vh2 = vpi_handle_by_index(vh1, 2);
        CHECK_RESULT_NZ(vh2);
        CHECK_RESULT(vpi_get(vpiSize, vh2), 32);  // 8*4

        // Index into second packed dim -> 8-bit word
        TestVpiHandle vh3 = vpi_handle_by_index(vh2, 2);
        CHECK_RESULT_NZ(vh3);
        CHECK_RESULT(vpi_get(vpiSize, vh3), 8);
        vpi_get_value(vh3, &v);
        CHECK_RESULT(v.value.integer, 74);  // 1*64 + 2*4 + 2

        // Further into bit level
        TestVpiHandle vh4 = vpi_handle_by_index(vh3, 3);
        CHECK_RESULT_NZ(vh4);
        CHECK_RESULT(vpi_get(vpiSize, vh4), 1);

        // Write last 32 bits of the packed vector in the specified unpacked dimension,
        // i.e. the four 8-bit elements in multi_packed[1][15][0:3]
        v.value.integer = 0xAABBCCDD;
        vpi_put_value(vh1, &v, nullptr, vpiNoDelay);

        // Index into the last element of the packed array and check value
        TestVpiHandle vh_last
            = vpi_handle_by_name((PLI_BYTE8*)"t.multi_packed[1][15][3]", nullptr);
        CHECK_RESULT_NZ(vh_last);
        vpi_get_value(vh_last, &v);
        CHECK_RESULT(v.value.integer, 0xDD);

        // Negative indices: negative_multi_packed is defined as
        // `[8:-7] [3:-4] negative_multi_packed[0:-2]`
        TestVpiHandle vh_neg
            = vpi_handle_by_name((PLI_BYTE8*)"t.negative_multi_packed[-1]", nullptr);
        CHECK_RESULT_NZ(vh_neg);
        CHECK_RESULT(vpi_get(vpiSize, vh_neg), 128);
        TestVpiHandle vh_neg_packed = vpi_handle_by_index(vh_neg, -2);
        CHECK_RESULT_NZ(vh_neg_packed);
        CHECK_RESULT(vpi_get(vpiSize, vh_neg_packed), 8);
        vpi_get_value(vh_neg_packed, &v);
        CHECK_RESULT(v.value.integer, 4);
        // Further into bit level
        TestVpiHandle vh_neg_bit = vpi_handle_by_index(vh_neg_packed, -2);
        CHECK_RESULT_NZ(vh_neg_bit);
        CHECK_RESULT(vpi_get(vpiSize, vh_neg_bit), 1);
        vpi_get_value(vh_neg_bit, &v);
        CHECK_RESULT(v.value.integer, 1);
    }

    // Partial indexing (not all unpacked dimensions)
    {
        // mem_2d[1] partially indexes -> remaining [0:7] array
        TestVpiHandle vh_2d_part = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[1]", nullptr);
        CHECK_RESULT_NZ(vh_2d_part);
        CHECK_RESULT(vpi_get(vpiType, vh_2d_part), vpiRegArray);
        CHECK_RESULT(vpi_get(vpiSize, vh_2d_part), 8);
        TestVpiHandle vh_2d_elem = vpi_handle_by_index(vh_2d_part, 3);
        CHECK_RESULT_NZ(vh_2d_elem);
        CHECK_RESULT(vpi_get(vpiType, vh_2d_elem), vpiReg);
        CHECK_RESULT(vpi_get(vpiSize, vh_2d_elem), 8);

        // mem_3d[0] partially indexes -> remaining [1:0][0:1] = 2*2=4 elements
        TestVpiHandle vh_3d_part = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[0]", nullptr);
        CHECK_RESULT_NZ(vh_3d_part);
        CHECK_RESULT(vpi_get(vpiType, vh_3d_part), vpiRegArray);
        CHECK_RESULT(vpi_get(vpiSize, vh_3d_part), 4);
    }

    // Invalid syntax in vpi_handle_by_name
    {
        // Trailing text after indices
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][0]bar", nullptr));
        // Non-integer / non-decimal index values
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][abc]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0x2][3]", nullptr));
        // Index out of bounds
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[4][0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[-1][0]", nullptr));
        // Structural bracket errors
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0[0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][1", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[[0]][1]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][1]]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d0][1]", nullptr));
        // Whitespace in indices (unsupported)
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[ 0 ][ 1 ]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][1]  ", nullptr));
        // Plain identifier with whitespace before part-select (unsupported; only escaped
        // identifiers may have whitespace before a trailing part-select)
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.\\escaped_inst[0] .sig [3:0]", nullptr));
        // Indexing non-array signals
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.onebit[0]", nullptr));
        // Part-select on non-array signal
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.onebit[0:0]", nullptr));
        // Part-select on unpacked-only array
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.unpacked_only[3:0]", nullptr));
        // Range/slice syntax in non-last position or on unpacked dimensions
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][1:3]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0:2][0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0:2][1:4]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0+:2][0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0-:2][0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0:2]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[0:1][0][0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[0][0:1][0]", nullptr));
        // Part-select with remaining unpacked dims (not fully indexed)
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[0][7:0]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[0][0][7:0]", nullptr));
        // Part-select out of range: mem_2d[0][0] is 8 bits [7:0]
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][0][15:8]", nullptr));
        CHECK_RESULT_Z(vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[0][0][8:7]", nullptr));
    }

    // Bit-range part-select via vpi_handle_by_name
    {
        // Descending-range element: mem_2d[3][0] = 8'(((3 * 8) + 0)) = 24 = 0x18
        TestVpiHandle vh_desc_mid = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[3][0][7:4]", nullptr);
        CHECK_RESULT_NZ(vh_desc_mid);
        CHECK_RESULT(vpi_get(vpiSize, vh_desc_mid), 4);
        vpi_get_value(vh_desc_mid, &v);
        CHECK_RESULT(v.value.integer, 0x1);  // [7:4] of 0x18

        TestVpiHandle vh_desc_full
            = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[3][0][7:0]", nullptr);
        CHECK_RESULT_NZ(vh_desc_full);
        CHECK_RESULT(vpi_get(vpiSize, vh_desc_full), 8);
        vpi_get_value(vh_desc_full, &v);
        CHECK_RESULT(v.value.integer, 24);  // 0x18

        // Descending range that crosses zero
        TestVpiHandle vh_desc_cross
            = vpi_handle_by_name((PLI_BYTE8*)"t.negative_multi_packed[-1][-2][1:-3]", nullptr);
        CHECK_RESULT_NZ(vh_desc_cross);
        CHECK_RESULT(vpi_get(vpiSize, vh_desc_cross), 5);
        vpi_get_value(vh_desc_cross, &v);
        // Element [-1][-2] is 8'h4; elements are indexed as [3:-4], so bits [1:-3] = 0b00010
        CHECK_RESULT(v.value.integer, 2);

        // Ascending packed range behavior is explicit:
        // mem_3d has packed declaration [0:95], so [3:0] selects the MSB-end nibble,
        // while [92:95] selects the LSB-end nibble where value 7 resides.
        TestVpiHandle vh_asc_lsb
            = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1][92:95]", nullptr);
        CHECK_RESULT_NZ(vh_asc_lsb);
        CHECK_RESULT(vpi_get(vpiSize, vh_asc_lsb), 4);
        vpi_get_value(vh_asc_lsb, &v);
        CHECK_RESULT(v.value.integer, 7);  // [92:95] of 0x...000007

        // Select order [95:92] is also accepted and refers to the same bit set as [92:95].
        TestVpiHandle vh_asc_lsb_rev
            = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1][95:92]", nullptr);
        CHECK_RESULT_NZ(vh_asc_lsb_rev);
        CHECK_RESULT(vpi_get(vpiSize, vh_asc_lsb_rev), 4);
        vpi_get_value(vh_asc_lsb_rev, &v);
        CHECK_RESULT(v.value.integer, 7);

        TestVpiHandle vh_asc_mid
            = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1][90:94]", nullptr);
        CHECK_RESULT_NZ(vh_asc_mid);
        CHECK_RESULT(vpi_get(vpiSize, vh_asc_mid), 5);
        vpi_get_value(vh_asc_mid, &v);
        CHECK_RESULT(v.value.integer, 3);  // 5-bit window containing 0b00011

        TestVpiHandle vh_asc_mid_rev
            = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1][95:91]", nullptr);
        CHECK_RESULT_NZ(vh_asc_mid_rev);
        CHECK_RESULT(vpi_get(vpiSize, vh_asc_mid_rev), 5);
        vpi_get_value(vh_asc_mid_rev, &v);
        CHECK_RESULT(v.value.integer, 7);

        // Cross-order select on ascending declaration is allowed and maps by declared indices.
        TestVpiHandle vh_asc_msb
            = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1][3:0]", nullptr);
        CHECK_RESULT_NZ(vh_asc_msb);
        CHECK_RESULT(vpi_get(vpiSize, vh_asc_msb), 4);
        vpi_get_value(vh_asc_msb, &v);
        CHECK_RESULT(v.value.integer, 0);  // [3:0] is MSB-end for [0:95]

        // Part-select combined with array index: mem_2d[2][3] = 19 = 0x13
        TestVpiHandle vh_2d_arr = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[2][3][3:0]", nullptr);
        CHECK_RESULT_NZ(vh_2d_arr);
        CHECK_RESULT(vpi_get(vpiSize, vh_2d_arr), 4);
        vpi_get_value(vh_2d_arr, &v);
        CHECK_RESULT(v.value.integer, 0x3);

        // Equivalent ascending-order spelling of the MSB-end nibble
        TestVpiHandle vh_3d_ps = vpi_handle_by_name((PLI_BYTE8*)"t.mem_3d[1][1][1][0:3]", nullptr);
        CHECK_RESULT_NZ(vh_3d_ps);
        CHECK_RESULT(vpi_get(vpiSize, vh_3d_ps), 4);
        vpi_get_value(vh_3d_ps, &v);
        CHECK_RESULT(v.value.integer, 0);
    }

    // Part-select write: write 0x2 to mem_2d[3][0][7:4], verify only those bits change
    {
        TestVpiHandle vh_ps = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[3][0][7:4]", nullptr);
        CHECK_RESULT_NZ(vh_ps);

        s_vpi_value put_val;
        put_val.format = vpiIntVal;
        put_val.value.integer = 0x2;
        s_vpi_time time_s = {vpiSimTime, 0, 0, 0.0};
        vpi_put_value(vh_ps, &put_val, &time_s, vpiNoDelay);

        // Read back full element
        TestVpiHandle vh_full = vpi_handle_by_name((PLI_BYTE8*)"t.mem_2d[3][0]", nullptr);
        CHECK_RESULT_NZ(vh_full);
        vpi_get_value(vh_full, &v);
        CHECK_RESULT(v.value.integer, 0x28);  // 0x18 with bits [7:4] changed to 0x2

        // Restore original value
        put_val.value.integer = 0x1;
        vpi_put_value(vh_ps, &put_val, &time_s, vpiNoDelay);
    }

    return 0;
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
#ifdef TEST_VERBOSE
    printf("-mon_check()\n");
#endif

    if (int status = _mon_check_mcd()) return status;
    if (int status = _mon_check_callbacks()) return status;
    if (int status = _mon_check_value_callbacks()) return status;
    if (int status = _mon_check_var()) return status;
    if (int status = _mon_check_rev()) return status;
    if (int status = _mon_check_varlist()) return status;
    if (int status = _mon_check_var_long_name()) return status;
// Ports are not public_flat_rw in t_vpi_var
#if defined(T_VPI_VAR2) || defined(T_VPI_VAR3)
    if (int status = _mon_check_ports()) return status;
#endif
    if (int status = _mon_check_getput()) return status;
    if (int status = _mon_check_getput_iter()) return status;
    if (int status = _mon_check_quad()) return status;
    if (int status = _mon_check_string()) return status;
    if (int status = _mon_check_putget_str(NULL)) return status;
    if (int status = _mon_check_vlog_info()) return status;
    if (int status = _mon_check_multi_index()) return status;
    if (int status = _mon_check_delayed()) return status;
    if (int status = _mon_check_big()) return status;
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

    topp->clk = 0;
    topp->a = 0;

    topp->eval();
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
    CHECK_RESULT(callback_count, 501);
    CHECK_RESULT(callback_count_half, 250);
    CHECK_RESULT(callback_count_quad, 2);
    CHECK_RESULT(callback_count_strs, callback_count_strs_max);
    VerilatedVpi::clearEvalNeeded();
    if (VerilatedVpi::evalNeeded()) {
        vl_fatal(FILENM, __LINE__, "main", "%Error: Unexpected VPI dirty state");
    }
    touch_signal();
    if (!VerilatedVpi::evalNeeded()) {
        vl_fatal(FILENM, __LINE__, "main", "%Error: Unexpected VPI clean state");
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
