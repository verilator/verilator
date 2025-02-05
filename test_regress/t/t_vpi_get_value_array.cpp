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
#include "verilated_vpi.h"

#include "Vt_vpi_get_value_array.h"

#endif

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

#include <vector>

//======================================================================

int test_vpiRawFourStateVal(char* name, PLI_BYTE8* test_data, int index, const unsigned low,
                            const unsigned num, const unsigned size, const unsigned elem_size) {
#ifdef TEST_VERBOSE
    printf("%%\n%s: name=%s index=%u low=%u num=%u size=%u elem_size=%u\n\n", __func__, name,
           index, low, num, size, elem_size);
#endif

    // prepare index
    int index_arr[1] = {index};

    // get array handle
    TestVpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue;
    arrayvalue.format = vpiRawFourStateVal;
    arrayvalue.flags = 0;
    arrayvalue.value.vectors = 0;
    vpi_get_value_array(arrayhandle, &arrayvalue, index_arr, num);
    CHECK_RESULT_NZ(!vpi_chk_error(0));

    // compare to test data
    index -= low;
    for (unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
        for (unsigned j = 0; j < elem_size; j++) {
#ifdef TEST_VERBOSE
            printf("arr[%u] == test[%u]\n", (i * 2 * elem_size) + j, (offset * elem_size) + j);
#endif
            CHECK_RESULT_HEX(arrayvalue.value.rawvals[(i * 2 * elem_size) + j],
                             test_data[(offset * elem_size) + j]);
        }
        for (unsigned j = 0; j < elem_size; j++) {
            CHECK_RESULT_HEX(arrayvalue.value.rawvals[(((i * 2) + 1) * elem_size) + j], 0);
        }
    }

    return 0;
}

int test_vpiRawTwoStateVal(char* name, PLI_BYTE8* test_data, int index, const unsigned low,
                           const unsigned num, const unsigned size, const unsigned elem_size) {
#ifdef TEST_VERBOSE
    printf("%%\n%s: name=%s index=%u low=%u num=%u size=%u elem_size=%u\n\n", __func__, name,
           index, low, num, size, elem_size);
#endif

    // prepare index
    int index_arr[1] = {index};

    // get array handle
    TestVpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw two state
    s_vpi_arrayvalue arrayvalue;
    arrayvalue.format = vpiRawTwoStateVal;
    arrayvalue.flags = 0;
    arrayvalue.value.vectors = 0;
    vpi_get_value_array(arrayhandle, &arrayvalue, index_arr, num);
    CHECK_RESULT_NZ(!vpi_chk_error(0));

    // compare to test data
    index -= low;
    for (unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
        for (unsigned j = 0; j < elem_size; j++) {
#ifdef TEST_VERBOSE
            printf("arr[%u] == test[%u]\n", (i * elem_size) + j, (offset * elem_size) + j);
#endif
            CHECK_RESULT_HEX(arrayvalue.value.rawvals[(i * elem_size) + j],
                             test_data[(offset * elem_size) + j]);
        }
    }

    return 0;
}

int test_vpiVectorVal(char* name, PLI_BYTE8* test_data, int index, const unsigned low,
                      const unsigned num, const unsigned size, const unsigned elem_size) {
#ifdef TEST_VERBOSE
    printf("%%\n%s: name=%s index=%u low=%u num=%u size=%u elem_size=%u\n\n", __func__, name,
           index, low, num, size, elem_size);
#endif

    // prepare index
    int index_arr[1] = {index};
    const unsigned elem_size_words = (elem_size + 3) / sizeof(PLI_UINT32);
    const unsigned vec_size = elem_size_words * size;
    std::vector<s_vpi_vecval> test_data_vectors;
    test_data_vectors.reserve(vec_size);
    unsigned test_data_index = 0;
    for (unsigned i = 0; i < size; i++) {
        unsigned count = 0;
        for (unsigned j = 0; j < elem_size_words; j++) {
            PLI_UINT32& aval = test_data_vectors[(i * elem_size_words) + j].aval;
            test_data_vectors[(i * elem_size_words) + j].bval = UINT32_MAX;
            aval = 0;
            for (unsigned k = 0; k < sizeof(PLI_UINT32); k++) {
                if (count++ == elem_size) break;
                aval |= static_cast<PLI_UINT32>(test_data[test_data_index++] & 0xFF) << (k * 8);
            }
        }
    }

    // get array handle
    TestVpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test vector
    s_vpi_arrayvalue arrayvalue;
    arrayvalue.format = vpiVectorVal;
    arrayvalue.flags = 0;
    arrayvalue.value.vectors = 0;
    vpi_get_value_array(arrayhandle, &arrayvalue, index_arr, num);
    CHECK_RESULT_NZ(!vpi_chk_error(0));

#ifdef TEST_VERBOSE
    for (unsigned i = 0; i < vec_size; i++) {
        printf("arr[%u]=%x test[%u]=%x\n", i, arrayvalue.value.vectors[i].aval, i,
               test_data_vectors[i].aval);
    }
#endif

    // compare to test data
    index -= low;
    for (unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
        for (unsigned j = 0; j < elem_size_words; j++) {
#ifdef TEST_VERBOSE
            printf("array[%u] == test[%u]\n", (i * elem_size_words) + j,
                   (offset * elem_size_words) + j);
#endif
            CHECK_RESULT_HEX(arrayvalue.value.vectors[(i * elem_size_words) + j].aval,
                             test_data_vectors[(offset * elem_size_words) + j].aval);
            CHECK_RESULT_HEX(arrayvalue.value.vectors[(i * elem_size_words) + j].bval, 0);
        }
    }

    return 0;
}

int test_vpiIntVal(char* name, PLI_BYTE8* test_data, int index, const unsigned low,
                   const unsigned num, const unsigned size, const unsigned elem_size) {
#ifdef TEST_VERBOSE
    printf("%%\n%s: name=%s index=%u low=%u num=%u size=%u elem_size=%u\n\n", __func__, name,
           index, low, num, size, elem_size);
#endif

    // prepare index
    int index_arr[1] = {index};
    std::vector<PLI_INT32> test_data_integers;
    test_data_integers.reserve(size);
    for (unsigned i = 0; i < size; i++) {
        PLI_INT32& integer = test_data_integers[i];
        integer = 0;
        for (unsigned j = 0; j < elem_size; j++) {
            integer |= (static_cast<PLI_INT32>(test_data[(i * elem_size) + j]) & 0xFF) << (j * 8);
        }
    }

    // get array handle
    TestVpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue;
    arrayvalue.format = vpiIntVal;
    arrayvalue.flags = 0;
    arrayvalue.value.integers = 0;
    vpi_get_value_array(arrayhandle, &arrayvalue, index_arr, num);
    CHECK_RESULT_NZ(!vpi_chk_error(0));

#ifdef TEST_VERBOSE
    for (unsigned i = 0; i < size; i++) {
        printf("arr[%u]=%x test[%u]=%x\n", i, arrayvalue.value.integers[i], i,
               test_data_integers[i]);
    }
#endif

    // compare to test data
    index -= low;
    for (unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
#ifdef TEST_VERBOSE
        printf("array[%u] == test[%u]\n", i, offset);
#endif
        CHECK_RESULT_HEX(arrayvalue.value.integers[i], test_data_integers[offset]);
    }

    return 0;
}

int test_vpiShortIntVal(char* name, PLI_BYTE8* test_data, int index, const unsigned low,
                        const unsigned num, const unsigned size, const unsigned elem_size) {
#ifdef TEST_VERBOSE
    printf("%%\n%s: name=%s index=%u low=%u num=%u size=%u elem_size=%u\n\n", __func__, name,
           index, low, num, size, elem_size);
#endif

    // prepare index
    int index_arr[1] = {index};
    std::vector<PLI_INT16> test_data_shortints;
    test_data_shortints.reserve(size);
    for (unsigned i = 0; i < size; i++) {
        if (elem_size == 2) {
            test_data_shortints[i] = test_data[i * 2] & 0xFF;
            test_data_shortints[i] |= test_data[(i * 2) + 1] << 8;
        } else {
            test_data_shortints[i] = test_data[i] & 0xFF;
        }
    }

    // get array handle
    TestVpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue;
    arrayvalue.format = vpiShortIntVal;
    arrayvalue.flags = 0;
    arrayvalue.value.shortints = 0;
    vpi_get_value_array(arrayhandle, &arrayvalue, index_arr, num);
    CHECK_RESULT_NZ(!vpi_chk_error(0));

#ifdef TEST_VERBOSE
    for (unsigned i = 0; i < size; i++) {
        printf("arr[%u]=%x test[%u]=%x\n", i, arrayvalue.value.shortints[i], i,
               test_data_shortints[i]);
    }
#endif

    // compare to test data
    index -= low;
    for (unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
#ifdef TEST_VERBOSE
        printf("array[%u] == test[%u]\n", i, offset);
#endif
        CHECK_RESULT_HEX(arrayvalue.value.shortints[i], test_data_shortints[offset]);
    }

    return 0;
}

int test_vpiLongIntVal(char* name, PLI_BYTE8* test_data, int index, const unsigned low,
                       const unsigned num, const unsigned size, const unsigned elem_size) {
#ifdef TEST_VERBOSE
    printf("%%\n%s: name=%s index=%u low=%u num=%u size=%u elem_size=%u\n\n", __func__, name,
           index, low, num, size, elem_size);
#endif

    // prepare index
    int index_arr[1] = {index};
    std::vector<PLI_INT64> test_data_longints;
    test_data_longints.reserve(size);
    for (unsigned i = 0; i < size; i++) {
        PLI_INT64& longint = test_data_longints[i];
        longint = 0;
        for (unsigned j = 0; j < elem_size; j++) {
            longint |= (static_cast<PLI_INT64>(test_data[(i * elem_size) + j]) & 0xFF) << (j * 8);
        }
    }

    // get array handle
    TestVpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue;
    arrayvalue.format = vpiLongIntVal;
    arrayvalue.flags = 0;
    arrayvalue.value.longints = 0;
    vpi_get_value_array(arrayhandle, &arrayvalue, index_arr, num);
    CHECK_RESULT_NZ(!vpi_chk_error(0));

    // compare to test data
    index -= low;
    for (unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
#ifdef TEST_VERBOSE
        printf("array[%u] == test[%u]\n", i, offset);
#endif
        CHECK_RESULT_HEX(arrayvalue.value.longints[i], test_data_longints[offset]);
    }

    return 0;
}

int mon_check_props() {
    // skip test if not verilator (value_array accessors unimplemented in other sims)
    if (!TestSimulator::is_verilator()) {
#ifdef VERILATOR
        printf("TestSimulator indicating not verilator, but VERILATOR macro is defined\n");
        return 1;
#endif
        return 0;
    }

    const unsigned NUM_ELEMENTS = 4;

    PLI_BYTE8 read_bytes[NUM_ELEMENTS]
        = {static_cast<PLI_BYTE8>(0xad), static_cast<PLI_BYTE8>(0xde),
           static_cast<PLI_BYTE8>(0xef), static_cast<PLI_BYTE8>(0xbe)};

    PLI_BYTE8 read_shorts[NUM_ELEMENTS * 2] = {
        static_cast<PLI_BYTE8>(0xad), static_cast<PLI_BYTE8>(0xde), static_cast<PLI_BYTE8>(0xef),
        static_cast<PLI_BYTE8>(0xbe), static_cast<PLI_BYTE8>(0xfe), static_cast<PLI_BYTE8>(0xca),
        static_cast<PLI_BYTE8>(0x0d), static_cast<PLI_BYTE8>(0xf0)};

    PLI_BYTE8 read_words[NUM_ELEMENTS * 4] = {
        static_cast<PLI_BYTE8>(0xef), static_cast<PLI_BYTE8>(0xbe), static_cast<PLI_BYTE8>(0xad),
        static_cast<PLI_BYTE8>(0xde), static_cast<PLI_BYTE8>(0x0d), static_cast<PLI_BYTE8>(0xf0),
        static_cast<PLI_BYTE8>(0xfe), static_cast<PLI_BYTE8>(0xca), static_cast<PLI_BYTE8>(0x03),
        static_cast<PLI_BYTE8>(0x02), static_cast<PLI_BYTE8>(0x01), static_cast<PLI_BYTE8>(0x00),
        static_cast<PLI_BYTE8>(0x07), static_cast<PLI_BYTE8>(0x06), static_cast<PLI_BYTE8>(0x05),
        static_cast<PLI_BYTE8>(0x04)};

    PLI_BYTE8 read_longs[NUM_ELEMENTS * 8] = {
        static_cast<PLI_BYTE8>(0x0d), static_cast<PLI_BYTE8>(0xf0), static_cast<PLI_BYTE8>(0xfe),
        static_cast<PLI_BYTE8>(0xca), static_cast<PLI_BYTE8>(0xef), static_cast<PLI_BYTE8>(0xbe),
        static_cast<PLI_BYTE8>(0xad), static_cast<PLI_BYTE8>(0xde), static_cast<PLI_BYTE8>(0x07),
        static_cast<PLI_BYTE8>(0x06), static_cast<PLI_BYTE8>(0x05), static_cast<PLI_BYTE8>(0x04),
        static_cast<PLI_BYTE8>(0x03), static_cast<PLI_BYTE8>(0x02), static_cast<PLI_BYTE8>(0x01),
        static_cast<PLI_BYTE8>(0x00), static_cast<PLI_BYTE8>(0x0F), static_cast<PLI_BYTE8>(0x0E),
        static_cast<PLI_BYTE8>(0x0D), static_cast<PLI_BYTE8>(0x0C), static_cast<PLI_BYTE8>(0x0B),
        static_cast<PLI_BYTE8>(0x0A), static_cast<PLI_BYTE8>(0x09), static_cast<PLI_BYTE8>(0x08),
        static_cast<PLI_BYTE8>(0x17), static_cast<PLI_BYTE8>(0x16), static_cast<PLI_BYTE8>(0x15),
        static_cast<PLI_BYTE8>(0x14), static_cast<PLI_BYTE8>(0x13), static_cast<PLI_BYTE8>(0x12),
        static_cast<PLI_BYTE8>(0x11), static_cast<PLI_BYTE8>(0x10)};

    PLI_BYTE8 read_customs[NUM_ELEMENTS * 9] = {
        static_cast<PLI_BYTE8>(0x0d), static_cast<PLI_BYTE8>(0xf0), static_cast<PLI_BYTE8>(0xfe),
        static_cast<PLI_BYTE8>(0xca), static_cast<PLI_BYTE8>(0xef), static_cast<PLI_BYTE8>(0xbe),
        static_cast<PLI_BYTE8>(0xad), static_cast<PLI_BYTE8>(0xde), static_cast<PLI_BYTE8>(0x1A),
        static_cast<PLI_BYTE8>(0x07), static_cast<PLI_BYTE8>(0x06), static_cast<PLI_BYTE8>(0x05),
        static_cast<PLI_BYTE8>(0x04), static_cast<PLI_BYTE8>(0x03), static_cast<PLI_BYTE8>(0x02),
        static_cast<PLI_BYTE8>(0x01), static_cast<PLI_BYTE8>(0x00), static_cast<PLI_BYTE8>(0x15),
        static_cast<PLI_BYTE8>(0x0F), static_cast<PLI_BYTE8>(0x0E), static_cast<PLI_BYTE8>(0x0D),
        static_cast<PLI_BYTE8>(0x0C), static_cast<PLI_BYTE8>(0x0B), static_cast<PLI_BYTE8>(0x0A),
        static_cast<PLI_BYTE8>(0x09), static_cast<PLI_BYTE8>(0x08), static_cast<PLI_BYTE8>(0x0A),
        static_cast<PLI_BYTE8>(0x17), static_cast<PLI_BYTE8>(0x16), static_cast<PLI_BYTE8>(0x15),
        static_cast<PLI_BYTE8>(0x14), static_cast<PLI_BYTE8>(0x13), static_cast<PLI_BYTE8>(0x12),
        static_cast<PLI_BYTE8>(0x11), static_cast<PLI_BYTE8>(0x10), static_cast<PLI_BYTE8>(0x05)};

    char read_bytes_name[] = "test.read_bytes";
    char read_bytes_nonzero_index_name[] = "test.read_bytes_nonzero_index";
    char read_bytes_rl_name[] = "test.read_bytes_rl";
    char read_shorts_name[] = "test.read_shorts";
    char read_words_name[] = "test.read_words";
    char read_integers_name[] = "test.read_integers";
    char read_longs_name[] = "test.read_longs";
    char read_customs_name[] = "test.read_customs";
    char read_customs_nonzero_index_rl_name[] = "test.read_customs_nonzero_index_rl";

    for (unsigned i = 0; i < NUM_ELEMENTS; i++) {
        for (unsigned j = 0; j < (NUM_ELEMENTS + 1); j++) {
            if (test_vpiRawFourStateVal(read_bytes_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiRawFourStateVal(read_bytes_nonzero_index_name, read_bytes, i + 1, 1, j,
                                        NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiRawFourStateVal(read_bytes_rl_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiRawFourStateVal(read_shorts_name, read_shorts, i, 0, j, NUM_ELEMENTS, 2))
                return 1;
            if (test_vpiRawFourStateVal(read_words_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiRawFourStateVal(read_integers_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiRawFourStateVal(read_longs_name, read_longs, i, 0, j, NUM_ELEMENTS, 8))
                return 1;
            if (test_vpiRawFourStateVal(read_customs_name, read_customs, i, 0, j, NUM_ELEMENTS, 9))
                return 1;
            if (test_vpiRawFourStateVal(read_customs_nonzero_index_rl_name, read_customs, i + 1, 1,
                                        j, NUM_ELEMENTS, 9))
                return 1;

            if (test_vpiRawTwoStateVal(read_bytes_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiRawTwoStateVal(read_bytes_rl_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiRawTwoStateVal(read_bytes_nonzero_index_name, read_bytes, i + 1, 1, j,
                                       NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiRawTwoStateVal(read_shorts_name, read_shorts, i, 0, j, NUM_ELEMENTS, 2))
                return 1;
            if (test_vpiRawTwoStateVal(read_words_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiRawTwoStateVal(read_integers_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiRawTwoStateVal(read_longs_name, read_longs, i, 0, j, NUM_ELEMENTS, 8))
                return 1;
            if (test_vpiRawTwoStateVal(read_customs_name, read_customs, i, 0, j, NUM_ELEMENTS, 9))
                return 1;
            if (test_vpiRawTwoStateVal(read_customs_nonzero_index_rl_name, read_customs, i + 1, 1,
                                       j, NUM_ELEMENTS, 9))
                return 1;

            if (test_vpiVectorVal(read_bytes_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1)) return 1;
            if (test_vpiVectorVal(read_bytes_nonzero_index_name, read_bytes, i + 1, 1, j,
                                  NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiVectorVal(read_bytes_rl_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiVectorVal(read_shorts_name, read_shorts, i, 0, j, NUM_ELEMENTS, 2))
                return 1;
            if (test_vpiVectorVal(read_words_name, read_words, i, 0, j, NUM_ELEMENTS, 4)) return 1;
            if (test_vpiVectorVal(read_integers_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiVectorVal(read_longs_name, read_longs, i, 0, j, NUM_ELEMENTS, 8)) return 1;
            if (test_vpiVectorVal(read_customs_name, read_customs, i, 0, j, NUM_ELEMENTS, 9))
                return 1;
            if (test_vpiVectorVal(read_customs_nonzero_index_rl_name, read_customs, i + 1, 1, j,
                                  NUM_ELEMENTS, 9))
                return 1;

            if (test_vpiShortIntVal(read_bytes_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiShortIntVal(read_bytes_nonzero_index_name, read_bytes, i + 1, 1, j,
                                    NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiShortIntVal(read_bytes_rl_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiShortIntVal(read_shorts_name, read_shorts, i, 0, j, NUM_ELEMENTS, 2))
                return 1;

            if (test_vpiIntVal(read_bytes_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1)) return 1;
            if (test_vpiIntVal(read_bytes_nonzero_index_name, read_bytes, i + 1, 1, j,
                               NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiIntVal(read_bytes_rl_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1)) return 1;
            if (test_vpiIntVal(read_words_name, read_words, i, 0, j, NUM_ELEMENTS, 4)) return 1;
            if (test_vpiIntVal(read_integers_name, read_words, i, 0, j, NUM_ELEMENTS, 4)) return 1;

            if (test_vpiLongIntVal(read_bytes_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiLongIntVal(read_bytes_nonzero_index_name, read_bytes, i + 1, 1, j,
                                   NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiLongIntVal(read_bytes_rl_name, read_bytes, i, 0, j, NUM_ELEMENTS, 1))
                return 1;
            if (test_vpiLongIntVal(read_shorts_name, read_shorts, i, 0, j, NUM_ELEMENTS, 2))
                return 1;
            if (test_vpiLongIntVal(read_words_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiLongIntVal(read_integers_name, read_words, i, 0, j, NUM_ELEMENTS, 4))
                return 1;
            if (test_vpiLongIntVal(read_longs_name, read_longs, i, 0, j, NUM_ELEMENTS, 8))
                return 1;
        }
    }

    {
        // test unsupported format
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_longs", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiRealVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test unsupported foramt
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiShortRealVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test unsupported format
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_longs", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiTimeVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};
        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test unsupported TestVpiHandle
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiIntVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test unsupported type
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_scalar", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiIntVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test indexp out of bounds
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_bounds", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiIntVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {4};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));

        indexp[0] = 0;
        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test unsupported flags
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiIntVal;
        arrayvalue.flags = vpiUserAllocFlag;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test unsupported format & vltype combination
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiShortIntVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, NUM_ELEMENTS);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test num out of bounds
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiIntVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;
        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, &arrayvalue, indexp, 5);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test null arrayvalue
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, 0, indexp, 0);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    {
        // test null indexp
        TestVpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"test.read_words", NULL);
        CHECK_RESULT_NZ(object);

        s_vpi_arrayvalue arrayvalue;
        arrayvalue.format = vpiIntVal;
        arrayvalue.flags = 0;
        arrayvalue.value.integers = 0;

        vpi_get_value_array(object, &arrayvalue, 0, 0);
        CHECK_RESULT_NZ(vpi_chk_error(0));
    }

    return 0;
}

extern "C" int mon_check(void) { return mon_check_props(); }

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
    Verilated::commandArgs(argc, argv);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    const std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{contextp.get(), ""}};
    contextp->fatalOnVpiError(0);

#ifdef VERILATOR
#ifdef TEST_VERBOSE
    contextp->scopesDump();
#endif
#endif

    while (!contextp->gotFinish()) { top->eval(); }

    return 0;
}
#endif
