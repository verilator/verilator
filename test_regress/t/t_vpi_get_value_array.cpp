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

#include "Vt_vpi_get_value_array.h"
#include "Vt_vpi_get_value_array__Dpi.h"
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
        printf("%%Error: %s:%d GOT = 0x%lx EXP = 0x%lx\n", FILENM, __LINE__, \
            static_cast<uint64_t>(got), static_cast<uint64_t>(exp)); \
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
    s_vpi_arrayvalue arrayVal = {0, 0, {NULL}};
    int indexArr[2] = {0};
    int num = 4;
    const int size = 4;

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_bytes", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiRawTwoStateVal, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);
        CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

        PLI_BYTE8* ptr = arrayVal.value.rawvals;

        PLI_BYTE8 expected[4] = {
            static_cast<PLI_BYTE8>(0xde),
            static_cast<PLI_BYTE8>(0xad),
            static_cast<PLI_BYTE8>(0xbe),
            static_cast<PLI_BYTE8>(0xef)};

        for (int i = 0; i < num; i++){
            CHECK_RESULT_HEX(ptr[i], expected[(indexArr[0] + i) % size]);
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_shorts", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiShortIntVal, 0, nullptr};
        int indexArr[1] = {rand() & size};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);
        CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

        PLI_INT16* ptr = arrayVal.value.shortints;

        PLI_INT16 expected[4] = {
            static_cast<PLI_INT16>(0xdead),
            static_cast<PLI_INT16>(0xbeef),
            static_cast<PLI_INT16>(0xcafe),
            static_cast<PLI_INT16>(0xf00d)};

        for (int i = 0; i < num; i++) {
            const unsigned element_offset = (indexArr[0] + i) % size;
            CHECK_RESULT_HEX(ptr[i], expected[element_offset]);
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_INT32* ptr = arrayVal.value.integers;

        PLI_INT32 expected[4] = {
            static_cast<PLI_INT32>(0xcafef00d),
            static_cast<PLI_INT32>(0xdeadbeef),
            static_cast<PLI_INT32>(0x01234567),
            static_cast<PLI_INT32>(0x89abcdef)};

        for (int i = 0; i < num; i++) {
            const unsigned element_offset = (indexArr[0] + i) % size;
            CHECK_RESULT_HEX(ptr[i], expected[element_offset]);
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words_rl", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);
        CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

        PLI_INT32* ptr = arrayVal.value.integers;

        PLI_INT32 expected[4] = {
            static_cast<PLI_INT32>(0xdeadbeef),
            static_cast<PLI_INT32>(0xcafef00d),
            static_cast<PLI_INT32>(0x01234567),
            static_cast<PLI_INT32>(0x89abcdef)};

        unsigned element_offset = indexArr[0];
        for (int i = 0; i < num; i++) {
            CHECK_RESULT_HEX(ptr[i], expected[element_offset]);
            element_offset = element_offset == 0 ? size - 1 : element_offset - 1;
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_longs", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiLongIntVal, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);
        CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

        PLI_INT64* ptr = arrayVal.value.longints;

        PLI_INT64 expected[4] = {
            static_cast<PLI_INT64>(0xdeadbeefcafef00d),
            static_cast<PLI_INT64>(0x0123456789abcdef),
            static_cast<PLI_INT64>(0xbeefdeadf00dcafe),
            static_cast<PLI_INT64>(0x45670123cdef89ab)};

        for (int i = 0; i < num; i++) {
            const unsigned element_offset = (indexArr[0] + i) % size;
            CHECK_RESULT_HEX(ptr[i], expected[element_offset]);
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_unorthodox", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiRawTwoStateVal, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = 4 % (size + 1);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UBYTE8* ptr = (PLI_UBYTE8*)arrayVal.value.rawvals;

        PLI_UINT32 expected[12] = {
            0xcafef00d,0xdeadbeef,0x0,
            0x89abcdef,0x01234567,0x1,
            0xf00dcafe,0xbeefdead,0x2,
            0xcdef89ab,0x45670123,0x3
        };

        const unsigned element_size_words = 3;
        const unsigned element_size_bytes = 9;
        unsigned element_offset = indexArr[0];
        for (int i = 0; i < (num * 9); i++) {
            const unsigned byte_offset = (i % element_size_bytes);
            const unsigned word_offset = (element_offset * element_size_words) + (byte_offset / 4);
            const uint32_t data_word = expected[word_offset];
            const uint8_t data_byte = (data_word >> ((byte_offset & 0x3)*8)) & 0xFF;
            CHECK_RESULT_HEX(ptr[i],data_byte);

            if (byte_offset == (element_size_bytes - 1)) {
                element_offset = element_offset == size - 1 ? 0 : element_offset + 1;
            }
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_unorthodox_rl", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiRawTwoStateVal, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = 4 % (size + 1);
        vpi_get_value_array(object, &arrayVal, indexArr, num);

        PLI_UBYTE8* ptr = (PLI_UBYTE8*)arrayVal.value.rawvals;

        PLI_UINT32 expected[12] = {
            0xcafef00d,0xdeadbeef,0x0,
            0x89abcdef,0x01234567,0x1,
            0xf00dcafe,0xbeefdead,0x2,
            0xcdef89ab,0x45670123,0x3
        };

        const unsigned element_size_words = 3;
        const unsigned element_size_bytes = 9;
        unsigned element_offset = indexArr[0];
        for (int i = 0; i < (num * 9); i++) {
            const unsigned byte_offset = (i % element_size_bytes);
            const unsigned word_offset = (element_offset * element_size_words) + (byte_offset / 4);
            const uint32_t data_word = expected[word_offset];
            const uint8_t data_byte = (data_word >> ((byte_offset & 0x3)*8)) & 0xFF;
            CHECK_RESULT_HEX(ptr[i],data_byte);

            if (byte_offset == (element_size_bytes - 1)) {
                element_offset = element_offset == 0 ? size - 1 : element_offset - 1;
            }
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiVector, 0, nullptr};
        int indexArr[1] = {rand() % size};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);
        CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

        p_vpi_vecval ptr = arrayVal.value.vectors;

        PLI_INT32 expected[4] = {
            static_cast<PLI_INT32>(0xcafef00d),
            static_cast<PLI_INT32>(0xdeadbeef),
            static_cast<PLI_INT32>(0x01234567),
            static_cast<PLI_INT32>(0x89abcdef)};

        for (int i = 0; i < num; i++) {
            const unsigned element_offset = (indexArr[0] + i) % size;
            CHECK_RESULT_HEX(ptr[i].aval, expected[element_offset]);
            CHECK_RESULT_HEX(ptr[i].bval, 0);
        }
    }

    {
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_integers", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal = {vpiIntVal, 0, nullptr};
        int indexArr[1] = {rand() & 0x3};
        int num = rand() % (size + 1);

        vpi_get_value_array(object, &arrayVal, indexArr, num);
        CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

        PLI_INT32* ptr = arrayVal.value.integers;

        PLI_INT32 expected[4] = {
            INT32_MIN,
            INT32_MAX,
            0,
            1234567890};

        for (int i = 0; i < num; i++) {
            const unsigned element_offset = (indexArr[0] + i) % size;
            CHECK_RESULT_HEX(ptr[i], expected[element_offset]);
        }
    }

    {
        // test unsupported format
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_longs", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiRealVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported foramt
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiShortRealVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported format
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_longs", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiTimeVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported vpiHandle
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test",NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported type
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_scalar",NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test indexp out of bounds
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_bounds",NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, nullptr};
        PLI_INT32 indexp[1] = {4};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));

        indexp[1] = {0};
        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported flags
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words",NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal = {vpiIntVal, vpiUserAllocFlag, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported format & vltype combination
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words",NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal = {vpiShortIntVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, num);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test num out of bounds
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.read_words",NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, nullptr};
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayVal, indexp, 5);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
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
    contextp->fatalOnVpiError(0);
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
