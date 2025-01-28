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

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

#ifdef TEST_VERBOSE
#define TEST_MSG printf
#else
#define TEST_MSG
#endif

//======================================================================

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

int test_vpiRawFourStateVal(char * name, PLI_BYTE8 * test_data, int index, const unsigned num, const unsigned size, const unsigned elem_size) {
    TEST_MSG("%%\n%s: name=%s index=%u num=%u size=%u elem_size=%u\n\n",__func__,name,index,num,size,elem_size);

    // prepare index and test data arrays
    int index_arr[1] = {index};
    PLI_BYTE8 test_data_four_state[size*elem_size*2];
    for(unsigned i = 0; i < size; i++) {
        for(unsigned j = 0; j < elem_size; j++) {
            test_data_four_state[(i*2*elem_size) + j] = test_data[(i*elem_size) + j];
        }
        for(unsigned j = 0; j < elem_size; j++) {
            test_data_four_state[(((i*2)+1)*elem_size)+j] = 1;// bval should be ignored
        }
    }

    // get array handle
    vpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue{vpiRawFourStateVal,0,nullptr};
    arrayvalue.value.rawvals = test_data_four_state;
    vpi_put_value_array(arrayhandle,&arrayvalue,index_arr,num);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // get value to check
    arrayvalue.value.rawvals = nullptr;
    vpi_get_value_array(arrayhandle,&arrayvalue,index_arr,size);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    for(unsigned i = 0; i < (2*size*elem_size); i++) {
        TEST_MSG("arr[%u]=%x test[%u]=%x\n",i,arrayvalue.value.rawvals[i] & 0xFF,i,test_data_four_state[i] & 0xFF);
    }

    // compare to test data
    for(unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
        for(unsigned j = 0; j < elem_size; j++) {
            TEST_MSG("arr[%u] == test[%u]\n",(i*2*elem_size) + j,(i*elem_size) + j);
            CHECK_RESULT_HEX(arrayvalue.value.rawvals[(i*2*elem_size) + j],test_data[(i*elem_size) + j]);
        }
        for(unsigned j = 0; j < elem_size; j++) {
            CHECK_RESULT_HEX(arrayvalue.value.rawvals[(((i*2)+1)*elem_size)+j],0);
        }
    }

    return 0;
}

int test_vpiRawTwoStateVal(char * name, PLI_BYTE8 * test_data, int index, const unsigned num, const unsigned size, const unsigned elem_size) {
    TEST_MSG("%%\n%s: name=%s index=%u num=%u size=%u elem_size=%u\n\n",__func__,name,index,num,size,elem_size);

    // prepare index
    int index_arr[1] = {index};

    // get array handle
    vpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue{vpiRawTwoStateVal,0,nullptr};
    arrayvalue.value.rawvals = test_data;
    vpi_put_value_array(arrayhandle,&arrayvalue,index_arr,num);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // get value to check
    arrayvalue.value.rawvals = nullptr;
    vpi_get_value_array(arrayhandle,&arrayvalue,index_arr,size);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    for(unsigned i = 0; i < (size*elem_size); i++) {
        TEST_MSG("arr[%u]=%x test[%u]=%x\n",i,arrayvalue.value.rawvals[i] & 0xFF,i,test_data[i] & 0xFF);
    }

    // compare to test data
    for(unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
        for(unsigned j = 0; j < elem_size; j++) {
            TEST_MSG("arr[%u] == test[%u]\n",(i*elem_size) + j,(i*elem_size) + j);
            CHECK_RESULT_HEX(arrayvalue.value.rawvals[(i*elem_size) + j],test_data[(i*elem_size) + j]);
        }
    }

    return 0;
}

int test_vpiVectorVal(char * name, PLI_BYTE8 * test_data, int index, const unsigned num, const unsigned size, const unsigned elem_size) {
    TEST_MSG("%%\n%s: name=%s index=%u num=%u size=%u elem_size=%u\n\n",__func__,name,index,num,size,elem_size);

    // prepare index
    int index_arr[1] = {index};
    const unsigned elem_size_words = (elem_size + 3) / sizeof(PLI_UINT32);
    const unsigned vec_size = elem_size_words * size;
    s_vpi_vecval test_data_vectors[vec_size];
    const s_vpi_vecval init_val{0,UINT32_MAX};
    std::fill(test_data_vectors,test_data_vectors+vec_size,init_val);
    unsigned test_data_index = 0;
    for(unsigned i = 0; i < size; i++){
        unsigned count = 0;
        for(unsigned j = 0; j < elem_size_words; j++) {
            PLI_UINT32 & aval = test_data_vectors[(i*elem_size_words) + j].aval;
            for(unsigned k = 0; k < sizeof(PLI_UINT32); k++) {
                if(count++ == elem_size) break;
                aval |= static_cast<PLI_UINT32>(test_data[test_data_index++] & 0xFF) << (k*8);
            }
        }
    }

    // get array handle
    vpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue{vpiVectorVal,0,nullptr};
    arrayvalue.value.vectors = test_data_vectors;
    vpi_put_value_array(arrayhandle,&arrayvalue,index_arr,num);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // get value to check
    arrayvalue.value.vectors = nullptr;
    vpi_get_value_array(arrayhandle,&arrayvalue,index_arr,size);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    for(unsigned i = 0; i < vec_size; i++) {
        TEST_MSG("arr[%u]=%x test[%u]=%x\n",i,arrayvalue.value.vectors[i].aval,i,test_data_vectors[i].aval);
    }

    // compare to test data
    for(unsigned i = 0; i < num; i++) {
        const unsigned offset = (index + i) % size;
        for(unsigned j = 0; j < elem_size_words; j++) {
            TEST_MSG("arr[%u] == test[%u]\n",(i*elem_size_words) + j,(i*elem_size_words) + j);
            CHECK_RESULT_HEX(arrayvalue.value.vectors[(i*elem_size_words) + j].aval,test_data_vectors[(i*elem_size_words) + j].aval);
        }
        for(unsigned j = 0; j < elem_size_words; j++) {
            CHECK_RESULT_HEX(arrayvalue.value.vectors[(i*elem_size_words) + j].bval, 0);
        }
    }

    return 0;
}

int test_vpiIntVal(char * name, PLI_BYTE8 * test_data, int index, const unsigned num, const unsigned size, const unsigned elem_size) {
    TEST_MSG("%%\n%s: name=%s index=%u num=%u size=%u elem_size=%u\n\n",__func__,name,index,num,size,elem_size);

    // prepare index
    int index_arr[1] = {index};
    PLI_INT32 test_data_integers[size];
    std::fill(test_data_integers,test_data_integers+size,0);
    for(unsigned i = 0; i < size; i++){
        PLI_INT32 & integer = test_data_integers[i];
        for(unsigned j = 0; j < elem_size; j++) {
            integer |= (static_cast<PLI_INT32>(test_data[(i*elem_size)+j]) & 0xFF) << (j*8);
        }
    }

    // get array handle
    vpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue{vpiIntVal,0,nullptr};
    arrayvalue.value.integers = test_data_integers;
    vpi_put_value_array(arrayhandle,&arrayvalue,index_arr,num);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // get value to check
    arrayvalue.value.vectors = nullptr;
    vpi_get_value_array(arrayhandle,&arrayvalue,index_arr,size);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    for(unsigned i = 0; i < size; i++) {
        TEST_MSG("arr[%u]=%x test[%u]=%x\n",i,arrayvalue.value.integers[i],i,test_data_integers[i]);
    }

    // compare to test data
    for(unsigned i = 0; i < num; i++) {
        TEST_MSG("arr[%u] == test[%u]\n",i,i);
        CHECK_RESULT_HEX(arrayvalue.value.integers[i],test_data_integers[i]);
    }

    return 0;
}

int test_vpiShortIntVal(char * name, PLI_BYTE8 * test_data, int index, const unsigned num, const unsigned size, const unsigned elem_size) {
    TEST_MSG("%%\n%s: name=%s index=%u num=%u size=%u elem_size=%u\n\n",__func__,name,index,num,size,elem_size);

    // prepare index
    int index_arr[1] = {index};
    PLI_INT16 test_data_shortints[size];
    for(unsigned i = 0; i < size; i++){
        if(elem_size == 2) {
            test_data_shortints[i] = test_data[i*2] & 0xFF;
            test_data_shortints[i] |= test_data[(i*2)+1] << 8;
        }else {
            test_data_shortints[i] = test_data[i] & 0xFF;
        }
    }

    // get array handle
    vpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue{vpiShortIntVal,0,nullptr};
    arrayvalue.value.shortints = test_data_shortints;
    vpi_put_value_array(arrayhandle,&arrayvalue,index_arr,num);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // get value to check
    arrayvalue.value.vectors = nullptr;
    vpi_get_value_array(arrayhandle,&arrayvalue,index_arr,size);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    for(unsigned i = 0; i < size; i++) {
        TEST_MSG("arr[%u]=%x test[%u]=%x\n",i,arrayvalue.value.shortints[i],i,test_data_shortints[i]);
    }

    // compare to test data
    for(unsigned i = 0; i < num; i++) {
        TEST_MSG("arr[%u] == test[%u]\n",i,i);
        CHECK_RESULT_HEX(arrayvalue.value.shortints[i],test_data_shortints[i]);
    }

    return 0;
}

int test_vpiLongIntVal(char * name, PLI_BYTE8 * test_data, int index, const unsigned num, const unsigned size, const unsigned elem_size) {
    TEST_MSG("%%\n%s: name=%s index=%u num=%u size=%u elem_size=%u\n\n",__func__,name,index,num,size,elem_size);

    // prepare index
    int index_arr[1] = {index};
    PLI_INT64 test_data_longints[size];
    for(unsigned i = 0; i < size; i++){
        PLI_INT64 & longint = test_data_longints[i];
        longint = 0;
        for(unsigned j = 0; j < elem_size; j++) {
            longint |= (static_cast<PLI_INT64>(test_data[(i*elem_size)+j]) & 0xFF) << (j*8);
        }
    }

    // get array handle
    vpiHandle arrayhandle = vpi_handle_by_name(name, NULL);
    CHECK_RESULT_NZ(arrayhandle);

    // test raw fourstate
    s_vpi_arrayvalue arrayvalue{vpiLongIntVal,0,nullptr};
    arrayvalue.value.longints = test_data_longints;
    vpi_put_value_array(arrayhandle,&arrayvalue,index_arr,num);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // get value to check
    arrayvalue.value.vectors = nullptr;
    vpi_get_value_array(arrayhandle,&arrayvalue,index_arr,size);
    CHECK_RESULT_NZ(!vpi_chk_error(nullptr));

    // compare to test data
    for(unsigned i = 0; i < num; i++) {
        TEST_MSG("arr[%u] == test[%u]\n",i,i);
        CHECK_RESULT_HEX(arrayvalue.value.longints[i],test_data_longints[i]);
    }

    return 0;
}

int mon_check_props(void) {
    const unsigned NUM_ELEMENTS = 4;

    PLI_BYTE8 write_bytes[NUM_ELEMENTS] = {
        static_cast<PLI_BYTE8>(0xad),
        static_cast<PLI_BYTE8>(0xde),
        static_cast<PLI_BYTE8>(0xef),
        static_cast<PLI_BYTE8>(0xbe)};

    PLI_BYTE8 write_shorts[NUM_ELEMENTS*2] = {
        static_cast<PLI_BYTE8>(0xad),
        static_cast<PLI_BYTE8>(0xde),
        static_cast<PLI_BYTE8>(0xef),
        static_cast<PLI_BYTE8>(0xbe),
        static_cast<PLI_BYTE8>(0xfe),
        static_cast<PLI_BYTE8>(0xca),
        static_cast<PLI_BYTE8>(0x0d),
        static_cast<PLI_BYTE8>(0xf0)};

    PLI_BYTE8 write_words[NUM_ELEMENTS*4] = {
        static_cast<PLI_BYTE8>(0xef),
        static_cast<PLI_BYTE8>(0xbe),
        static_cast<PLI_BYTE8>(0xad),
        static_cast<PLI_BYTE8>(0xde),
        static_cast<PLI_BYTE8>(0x0d),
        static_cast<PLI_BYTE8>(0xf0),
        static_cast<PLI_BYTE8>(0xfe),
        static_cast<PLI_BYTE8>(0xca),
        static_cast<PLI_BYTE8>(0x03),
        static_cast<PLI_BYTE8>(0x02),
        static_cast<PLI_BYTE8>(0x01),
        static_cast<PLI_BYTE8>(0x00),
        static_cast<PLI_BYTE8>(0x07),
        static_cast<PLI_BYTE8>(0x06),
        static_cast<PLI_BYTE8>(0x05),
        static_cast<PLI_BYTE8>(0x04)};

    PLI_BYTE8 write_longs[NUM_ELEMENTS*8] = {
        static_cast<PLI_BYTE8>(0x0d),
        static_cast<PLI_BYTE8>(0xf0),
        static_cast<PLI_BYTE8>(0xfe),
        static_cast<PLI_BYTE8>(0xca),
        static_cast<PLI_BYTE8>(0xef),
        static_cast<PLI_BYTE8>(0xbe),
        static_cast<PLI_BYTE8>(0xad),
        static_cast<PLI_BYTE8>(0xde),
        static_cast<PLI_BYTE8>(0x07),
        static_cast<PLI_BYTE8>(0x06),
        static_cast<PLI_BYTE8>(0x05),
        static_cast<PLI_BYTE8>(0x04),
        static_cast<PLI_BYTE8>(0x03),
        static_cast<PLI_BYTE8>(0x02),
        static_cast<PLI_BYTE8>(0x01),
        static_cast<PLI_BYTE8>(0x00),
        static_cast<PLI_BYTE8>(0x0F),
        static_cast<PLI_BYTE8>(0x0E),
        static_cast<PLI_BYTE8>(0x0D),
        static_cast<PLI_BYTE8>(0x0C),
        static_cast<PLI_BYTE8>(0x0B),
        static_cast<PLI_BYTE8>(0x0A),
        static_cast<PLI_BYTE8>(0x09),
        static_cast<PLI_BYTE8>(0x08),
        static_cast<PLI_BYTE8>(0x17),
        static_cast<PLI_BYTE8>(0x16),
        static_cast<PLI_BYTE8>(0x15),
        static_cast<PLI_BYTE8>(0x14),
        static_cast<PLI_BYTE8>(0x13),
        static_cast<PLI_BYTE8>(0x12),
        static_cast<PLI_BYTE8>(0x11),
        static_cast<PLI_BYTE8>(0x10)};

    PLI_BYTE8 write_customs[NUM_ELEMENTS*9] = {
        static_cast<PLI_BYTE8>(0x0d),
        static_cast<PLI_BYTE8>(0xf0),
        static_cast<PLI_BYTE8>(0xfe),
        static_cast<PLI_BYTE8>(0xca),
        static_cast<PLI_BYTE8>(0xef),
        static_cast<PLI_BYTE8>(0xbe),
        static_cast<PLI_BYTE8>(0xad),
        static_cast<PLI_BYTE8>(0xde),
        static_cast<PLI_BYTE8>(0x1A),
        static_cast<PLI_BYTE8>(0x07),
        static_cast<PLI_BYTE8>(0x06),
        static_cast<PLI_BYTE8>(0x05),
        static_cast<PLI_BYTE8>(0x04),
        static_cast<PLI_BYTE8>(0x03),
        static_cast<PLI_BYTE8>(0x02),
        static_cast<PLI_BYTE8>(0x01),
        static_cast<PLI_BYTE8>(0x00),
        static_cast<PLI_BYTE8>(0x15),
        static_cast<PLI_BYTE8>(0x0F),
        static_cast<PLI_BYTE8>(0x0E),
        static_cast<PLI_BYTE8>(0x0D),
        static_cast<PLI_BYTE8>(0x0C),
        static_cast<PLI_BYTE8>(0x0B),
        static_cast<PLI_BYTE8>(0x0A),
        static_cast<PLI_BYTE8>(0x09),
        static_cast<PLI_BYTE8>(0x08),
        static_cast<PLI_BYTE8>(0x0A),
        static_cast<PLI_BYTE8>(0x17),
        static_cast<PLI_BYTE8>(0x16),
        static_cast<PLI_BYTE8>(0x15),
        static_cast<PLI_BYTE8>(0x14),
        static_cast<PLI_BYTE8>(0x13),
        static_cast<PLI_BYTE8>(0x12),
        static_cast<PLI_BYTE8>(0x11),
        static_cast<PLI_BYTE8>(0x10),
        static_cast<PLI_BYTE8>(0x05)};

    char write_bytes_name[] = "TOP.test.write_bytes";
    char write_bytes_nonzero_index_name[] = "TOP.test.write_bytes_nonzero_index";
    char write_bytes_rl_name[] = "TOP.test.write_bytes_rl";
    char write_shorts_name[] = "TOP.test.write_shorts";
    char write_words_name[] = "TOP.test.write_words";
    char write_integers_name[] = "TOP.test.write_integers";
    char write_longs_name[] = "TOP.test.write_longs";
    char write_customs_name[] = "TOP.test.write_customs";
    char write_customs_nonzero_index_rl_name[] = "TOP.test.write_customs_nonzero_index_rl";

    for(unsigned i = 0; i < NUM_ELEMENTS; i++) {
        for(unsigned j = 0; j < (NUM_ELEMENTS + 1); j++) {
            if(test_vpiRawFourStateVal(write_bytes_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiRawFourStateVal(write_bytes_nonzero_index_name,write_bytes,i+1,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiRawFourStateVal(write_bytes_rl_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiRawFourStateVal(write_shorts_name,write_shorts,i,j,NUM_ELEMENTS,2)) return 1;
            if(test_vpiRawFourStateVal(write_words_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiRawFourStateVal(write_integers_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiRawFourStateVal(write_longs_name,write_longs,i,j,NUM_ELEMENTS,8)) return 1;
            if(test_vpiRawFourStateVal(write_customs_name,write_customs,i,j,NUM_ELEMENTS,9)) return 1;
            if(test_vpiRawFourStateVal(write_customs_nonzero_index_rl_name,write_customs,i+1,j,NUM_ELEMENTS,9)) return 1;

            if(test_vpiRawTwoStateVal(write_bytes_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiRawTwoStateVal(write_bytes_rl_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiRawTwoStateVal(write_bytes_nonzero_index_name,write_bytes,i+1,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiRawTwoStateVal(write_shorts_name,write_shorts,i,j,NUM_ELEMENTS,2)) return 1;
            if(test_vpiRawTwoStateVal(write_words_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiRawTwoStateVal(write_integers_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiRawTwoStateVal(write_longs_name,write_longs,i,j,NUM_ELEMENTS,8)) return 1;
            if(test_vpiRawTwoStateVal(write_customs_name,write_customs,i,j,NUM_ELEMENTS,9)) return 1;
            if(test_vpiRawTwoStateVal(write_customs_nonzero_index_rl_name,write_customs,i+1,j,NUM_ELEMENTS,9)) return 1;

            if(test_vpiVectorVal(write_bytes_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiVectorVal(write_bytes_nonzero_index_name,write_bytes,i+1,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiVectorVal(write_bytes_rl_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiVectorVal(write_shorts_name,write_shorts,i,j,NUM_ELEMENTS,2)) return 1;
            if(test_vpiVectorVal(write_words_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiVectorVal(write_integers_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiVectorVal(write_longs_name,write_longs,i,j,NUM_ELEMENTS,8)) return 1;
            if(test_vpiVectorVal(write_customs_name,write_customs,i,j,NUM_ELEMENTS,9)) return 1;
            if(test_vpiVectorVal(write_customs_nonzero_index_rl_name,write_customs,i+1,j,NUM_ELEMENTS,9)) return 1;

            if(test_vpiShortIntVal(write_bytes_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiShortIntVal(write_bytes_nonzero_index_name,write_bytes,i+1,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiShortIntVal(write_bytes_rl_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiShortIntVal(write_shorts_name,write_shorts,i,j,NUM_ELEMENTS,2)) return 1;

            if(test_vpiIntVal(write_bytes_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiIntVal(write_bytes_nonzero_index_name,write_bytes,i+1,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiIntVal(write_bytes_rl_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiIntVal(write_words_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiIntVal(write_integers_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;

            if(test_vpiLongIntVal(write_bytes_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiLongIntVal(write_bytes_nonzero_index_name,write_bytes,i+1,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiLongIntVal(write_bytes_rl_name,write_bytes,i,j,NUM_ELEMENTS,1)) return 1;
            if(test_vpiLongIntVal(write_shorts_name,write_shorts,i,j,NUM_ELEMENTS,2)) return 1;
            if(test_vpiLongIntVal(write_words_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiLongIntVal(write_integers_name,write_words,i,j,NUM_ELEMENTS,4)) return 1;
            if(test_vpiLongIntVal(write_longs_name,write_longs,i,j,NUM_ELEMENTS,8)) return 1;
        }
    }

    {
        // test unsupported format
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_longs", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue{vpiRealVal,0,datap};

        PLI_INT32 indexp[1] = {0};
        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));

        arrayvalue.format = vpiShortRealVal;
        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));

        arrayvalue.format = vpiTimeVal;
        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test null array value
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words", NULL);
        CHECK_RESULT_NZ(object);

        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, nullptr, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported vpiHandle
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiIntVal,0,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported type
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_scalar", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiIntVal,0,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test index out of bounds
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_bounds", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiIntVal,0,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));

        indexp[0] = {4};
        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test inaccessible
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_inaccessible", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiIntVal,0,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported flags
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiIntVal,vpiPropagateOff,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));

        arrayvalue.flags = vpiOneValue;
        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test unsupported format & type combination
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiShortIntVal,0,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));

        arrayvalue.flags = vpiOneValue;
        vpi_put_value_array(object, &arrayvalue, indexp, 4);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test num out of bounds
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words", NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayvalue = {vpiIntVal,0,datap};
        PLI_INT32 indexp[1] = {0};

        vpi_put_value_array(object, &arrayvalue, indexp, 5);
        CHECK_RESULT_NZ(~vpi_chk_error(nullptr));
    }

    {
        // test null arrayvalue
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words",NULL);
        CHECK_RESULT_NZ(object);

        PLI_INT32 indexp[1] = {0};

        vpi_get_value_array(object, nullptr, indexp, 0);
        CHECK_RESULT_NZ(vpi_chk_error(nullptr));
    }

    {
        // test null indexp
        vpiHandle object = vpi_handle_by_name((PLI_BYTE8*)"TOP.test.write_words",NULL);
        CHECK_RESULT_NZ(object);

        int datap[4] = {0,0,0,0};
        s_vpi_arrayvalue arrayVal{vpiIntVal, 0, datap};

        vpi_get_value_array(object, &arrayVal, nullptr, 0);
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
