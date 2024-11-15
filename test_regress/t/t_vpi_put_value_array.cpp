// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2024 by Diego Roux. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef IS_VPI

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_put_value_array.h"
#include "Vt_vpi_put_value_array__Dpi.h"
#include "svdpi.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

// __FILE__ is too long
#define FILENM "t_vpi_get_value_array.cpp"

#define TEST_MSG \
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
    if (std::strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", FILENM, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR_STRIP(got, exp) CHECK_RESULT_CSTR(got + strspn(got, " "), exp)

int mon_check_props(void) {
    s_vpi_arrayvalue arrayVal = {0, 0, NULL};
    int indexArr[2] = {0};
    int num = 4;

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_bytes", NULL);
        CHECK_RESULT_NZ(object);

        PLI_BYTE8 data[4] = {0xde, 0xad, 0xbe, 0xef};

        arrayVal.value.rawvals = data;
        arrayVal.format = vpiRawTwoStateVal;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_BYTE8* ptr = arrayVal.value.rawvals;

        for (int i = 0; i < num; i++)
            CHECK_RESULT_HEX(ptr[i], data[i]);
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_shorts", NULL);
        CHECK_RESULT_NZ(object);

        PLI_UINT16 data[4] = {0xdead, 0xbeef, 0xbeef, 0xdead};

        arrayVal.value.shortints = (PLI_INT16*)data;
        arrayVal.format = vpiShortIntVal;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UINT16* ptr = (PLI_UINT16*)arrayVal.value.shortints;

        for (int i = 0; i < num; i++)
            CHECK_RESULT_HEX(ptr[i], data[i]);
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_integers", NULL);
        CHECK_RESULT_NZ(object);

        PLI_UINT32 data[4] = {0x00000000, 0xdeadbeef, 0x00000000, 0xdeadbeef};

        arrayVal.value.integers = (PLI_INT32*)data;
        arrayVal.format = vpiIntVal;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UINT32* ptr = (PLI_UINT32*)arrayVal.value.integers;

        for (int i = 0; i < num; i++)
            CHECK_RESULT_HEX(ptr[i], data[i]);
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_integers_rl", NULL);
        CHECK_RESULT_NZ(object);

        indexArr[0] = 3;

        PLI_UINT32 data[4] = {0xdeadbeef, 0x00000000, 0xdeadbeef, 0x00000000};

        arrayVal.value.integers = (PLI_INT32*)data;
        arrayVal.format = vpiIntVal;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UINT32* ptr = (PLI_UINT32*)arrayVal.value.integers;

        for (int i = 0; i < num; i++)
            CHECK_RESULT_HEX(ptr[i], data[i]);

        indexArr[0] = 0;
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_longs", NULL);
        CHECK_RESULT_NZ(object);

        PLI_UINT64 data[4] = {0x00000000deadbeef, 0x0000000000000000,
                                0x00000000beefdead, 0x0000000000000000};

        arrayVal.value.longints = (PLI_INT64*)data;
        arrayVal.format = vpiLongIntVal;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UINT64* ptr = (PLI_UINT64*)arrayVal.value.longints;

        for (int i = 0; i < num; i++)
            CHECK_RESULT_HEX(ptr[i], data[i]);
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words", NULL);
        CHECK_RESULT_NZ(object);

        PLI_UINT64 data[16] = {0x0000000000000000, 0x0000000000000000, 0x00, 0x00,
            0xbeefdead00000000, 0x00000000deadbeef, 0x00, 0x00,
            0x0000000000000000, 0x00000000beefdead, 0x00, 0x00,
            0xbeefdeaddeadbeef, 0xbeefdeaddeadbeef, 0x00, 0x00};

        arrayVal.value.rawvals = (PLI_BYTE8*)data;
        arrayVal.format = vpiRawFourStateVal;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UINT64* ptr = (PLI_UINT64*)arrayVal.value.rawvals;

        for (int i = 0; i < num; i++)
            CHECK_RESULT_HEX(ptr[i], data[i]);
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_integers", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_vecval data[4] = {{0x00000000, 0x000000},
            {0xdeadbeef, 0x00000000}, {0x00000000, 0x00000000},
            {0xdeadbeef, 0x00000000}};

        arrayVal.value.vectors = data;
        arrayVal.format = vpiVector;

        vpi_put_value_array(object, &arrayVal, indexArr, num);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        p_vpi_vecval ptr = (p_vpi_vecval)arrayVal.value.vectors;

        for (int i = 0; i < num; i++) {
            CHECK_RESULT_HEX(ptr[i].aval, data[i].aval);
            CHECK_RESULT_HEX(ptr[i].bval, data[i].bval);
        }
    }

    return 0;
}

extern "C" int mon_check(void) {
    return mon_check_props();
}

#ifndef IS_VPI

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    const std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{contextp.get()}};

#ifdef TEST_VERBOSE
    contextp->internalsDump();
#endif

    while (!contextp->gotFinish()) {
        top->eval();
        VerilatedVpi::callValueCbs();
    }

    return 0;
}

#endif