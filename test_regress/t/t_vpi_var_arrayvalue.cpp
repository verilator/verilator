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

#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << FILENM << ":" << __LINE__ << ": GOT = " << +(got) \
                  << "   EXP = " << +(exp) << std::endl; \
        return __LINE__; \
    }

/*-------------------------------------------
TEST FUNCTIONS
-------------------------------------------*/

int _mon_check_get_bad(){
    // error on unsupported handle
    int index[2] = {0,0};
    s_vpi_arrayvalue bad_param_v = {vpiVectorVal,0,nullptr};
    TestVpiHandle bad_param_h = VPI_HANDLE("bad_param");
    CHECK_RESULT_NZ(bad_param_h);
    vpi_get_value_array(bad_param_h,&bad_param_v,index,1);
    CHECK_RESULT_NZ(vpi_chk_error(nullptr));

    // return on null value pointer
    TestVpiHandle bad_dim2_h = VPI_HANDLE("bad_dim2");
    CHECK_RESULT_NZ(bad_dim2_h);
    vpi_get_value_array(bad_dim2_h,nullptr,index,1);
    CHECK_RESULT_Z(vpi_chk_error(nullptr)); //also checks error reset

    // return on null index pointer
    s_vpi_arrayvalue bad_dim2_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(bad_dim2_h,&bad_dim2_v,nullptr,1);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));

    // error on unsupported handle format
    bad_dim2_v = s_vpi_arrayvalue{UINT32_MAX,0,nullptr};
    vpi_get_value_array(bad_dim2_h,&bad_dim2_v,index,1);
    CHECK_RESULT_NZ(vpi_chk_error(nullptr));

    // error on unsupported flags
    bad_dim2_v = s_vpi_arrayvalue{vpiVectorVal,UINT32_MAX,nullptr};
    vpi_get_value_array(bad_dim2_h,&bad_dim2_v,index,1);
    CHECK_RESULT_NZ(vpi_chk_error(nullptr));

    // error on unsupported dimensions
    TestVpiHandle bad_dim1_h = VPI_HANDLE("bad_dim1");
    CHECK_RESULT_NZ(bad_dim1_h);
    s_vpi_arrayvalue bad_dim1_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(bad_dim1_h,&bad_dim1_v,index,1);
    CHECK_RESULT_NZ(vpi_chk_error(nullptr));

    return 0;
}

int _mon_check_get_int(){
    // 2D vpiIntVal VLVT_UINT8 
    int index[2] = {0,0};
    TestVpiHandle int_dim2_8_h = VPI_HANDLE("int_dim2_8");
    CHECK_RESULT_NZ(int_dim2_8_h);
    s_vpi_arrayvalue int_dim2_v = {vpiIntVal,0,nullptr};
    vpi_get_value_array(int_dim2_8_h,&int_dim2_v,index,6);
    CHECK_RESULT_NZ(int_dim2_v.value.integers);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(int_dim2_v.value.integers[i],i+(1<<7));
    }

    // 2D vpiIntVal VLVT_UINT8 descending
    TestVpiHandle int_dim2_8_desc_h = VPI_HANDLE("int_dim2_8_desc");
    CHECK_RESULT_NZ(int_dim2_8_desc_h);
    s_vpi_arrayvalue int_dim2_8_desc_v = {vpiIntVal,0,nullptr};
    vpi_get_value_array(int_dim2_8_desc_h,&int_dim2_8_desc_v,index,6);
    CHECK_RESULT_NZ(int_dim2_8_desc_v.value.integers);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(int_dim2_8_desc_v.value.integers[i],i+(1<<7));
    }

    // 2D vpiIntVal VLVT_UINT8 userAllocFlag non-max num
    int_dim2_v = {vpiIntVal,vpiUserAllocFlag,nullptr};
    PLI_INT32 integers[6] = {0,0,0,0,0,0};
    int_dim2_v.value.integers = integers;
    vpi_get_value_array(int_dim2_8_h,&int_dim2_v,index,2);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        if(i >= 2) {
            CHECK_RESULT_Z(int_dim2_v.value.integers[i]);
            continue;
        }
        CHECK_RESULT(int_dim2_v.value.integers[i],i+(1<<7));
    }

    // 2D vpiIntVal VLVT_UINT8 non-zero index
    index[0] = 1;
    index[1] = 1;
    int_dim2_v = {vpiIntVal,0,nullptr};
    vpi_get_value_array(int_dim2_8_h,&int_dim2_v,index,6);
    CHECK_RESULT_NZ(int_dim2_v.value.integers);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(int_dim2_v.value.integers[i],((i+4)%6)+(1<<7));
    }

    // 2D vpiIntVal VLVT_UINT16
    index[0] = 0;
    index[1] = 0;
    TestVpiHandle int_dim2_16_h = VPI_HANDLE("int_dim2_16");
    CHECK_RESULT_NZ(int_dim2_16_h);
    int_dim2_v = {vpiIntVal,0,nullptr};
    vpi_get_value_array(int_dim2_16_h,&int_dim2_v,index,6);
    CHECK_RESULT_NZ(int_dim2_v.value.integers);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(int_dim2_v.value.integers[i],i+(1<<15));
    }

    // 2D vpiIntVal VLVT_UINT32
    TestVpiHandle int_dim2_32_h = VPI_HANDLE("int_dim2_32");
    CHECK_RESULT_NZ(int_dim2_32_h);
    int_dim2_v = {vpiIntVal,0,nullptr};
    vpi_get_value_array(int_dim2_32_h,&int_dim2_v,index,6);
    CHECK_RESULT_NZ(int_dim2_v.value.integers);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(int_dim2_v.value.integers[i],i+(1<<31));
    }

    return 0;
}

int _mon_check_get_vector(){
    // 2D vpiVectorVal VLVT_UINT8
    int index[2] = {0,0};
    TestVpiHandle vector_dim2_8_h = VPI_HANDLE("vector_dim2_8");
    CHECK_RESULT_NZ(vector_dim2_8_h);
    s_vpi_arrayvalue vector_dim2_8_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_8_h,&vector_dim2_8_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_8_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_8_v.value.vectors[i].aval,i+(1<<7));
        CHECK_RESULT_Z(vector_dim2_8_v.value.vectors[i].bval);
    }

    // 2D vpiVectorVal VLVT_UINT16
    TestVpiHandle vector_dim2_16_h = VPI_HANDLE("vector_dim2_16");
    CHECK_RESULT_NZ(vector_dim2_16_h);
    s_vpi_arrayvalue vector_dim2_16_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_16_h,&vector_dim2_16_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_16_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_16_v.value.vectors[i].aval,i+(1<<15));
        CHECK_RESULT_Z(vector_dim2_16_v.value.vectors[i].bval);
    }

    // 2D vpiVectorVal VLVT_UINT32
    TestVpiHandle vector_dim2_32_h = VPI_HANDLE("vector_dim2_32");
    CHECK_RESULT_NZ(vector_dim2_32_h);
    s_vpi_arrayvalue vector_dim2_32_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_32_h,&vector_dim2_32_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_32_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_32_v.value.vectors[i].aval,i+(1<<31));
        CHECK_RESULT_Z(vector_dim2_32_v.value.vectors[i].bval);
    }
    
    // 2D vpiVectorVal VLVT_UINT64
    TestVpiHandle vector_dim2_64_h = VPI_HANDLE("vector_dim2_64");
    CHECK_RESULT_NZ(vector_dim2_64_h);
    s_vpi_arrayvalue vector_dim2_64_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_64_h,&vector_dim2_64_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_64_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_64_v.value.vectors[(2*i)].aval,i);
        CHECK_RESULT(vector_dim2_64_v.value.vectors[(2*i)+1].aval,(1<<31));
        CHECK_RESULT_Z(vector_dim2_64_v.value.vectors[(2*i)].bval);
        CHECK_RESULT_Z(vector_dim2_64_v.value.vectors[(2*i)+1].bval);
    }

    // 2D vpiVectorVal VLVT_UINT64 non-zero index
    index[0] = 1;
    index[1] = 1;
    vector_dim2_64_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_64_h,&vector_dim2_64_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_64_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_64_v.value.vectors[(2*i)].aval,(i+4)%6);
        CHECK_RESULT(vector_dim2_64_v.value.vectors[(2*i)+1].aval,(1<<31));
        CHECK_RESULT_Z(vector_dim2_64_v.value.vectors[(2*i)].bval);
        CHECK_RESULT_Z(vector_dim2_64_v.value.vectors[(2*i)+1].bval);
    }

    // 2D vpiVectorVal VLVT_WData non-zero index
    TestVpiHandle vector_dim2_96_h = VPI_HANDLE("vector_dim2_96");
    CHECK_RESULT_NZ(vector_dim2_96_h);
    s_vpi_arrayvalue vector_dim2_96_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_96_h,&vector_dim2_96_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_96_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_96_v.value.vectors[(3*i)].aval,(i+4)%6);
        CHECK_RESULT(vector_dim2_96_v.value.vectors[(3*i)+1].aval,(1<<30));
        CHECK_RESULT(vector_dim2_96_v.value.vectors[(3*i)+2].aval,(1<<31));
        CHECK_RESULT_Z(vector_dim2_96_v.value.vectors[(3*i)].bval);
        CHECK_RESULT_Z(vector_dim2_96_v.value.vectors[(3*i)+1].bval);
        CHECK_RESULT_Z(vector_dim2_96_v.value.vectors[(3*i)+2].bval);
    }

    // 2D vpiVectorVal VLVT_WData
    index[0] = 0;
    index[1] = 0;
    vector_dim2_96_v = {vpiVectorVal,0,nullptr};
    vpi_get_value_array(vector_dim2_96_h,&vector_dim2_96_v,index,6);
    CHECK_RESULT_NZ(vector_dim2_96_v.value.vectors);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(vector_dim2_96_v.value.vectors[(3*i)].aval,i);
        CHECK_RESULT(vector_dim2_96_v.value.vectors[(3*i)+1].aval,(1<<30));
        CHECK_RESULT(vector_dim2_96_v.value.vectors[(3*i)+2].aval,(1<<31));
        CHECK_RESULT_Z(vector_dim2_96_v.value.vectors[(3*i)].bval);
        CHECK_RESULT_Z(vector_dim2_96_v.value.vectors[(3*i)+1].bval);
        CHECK_RESULT_Z(vector_dim2_96_v.value.vectors[(3*i)+2].bval);
    }

    return 0;
}

int _mon_check_get_real(){
    // 2D vpiRealVal
    int index[2] = {0,0};
    TestVpiHandle real_dim2_h = VPI_HANDLE("real_dim2");
    CHECK_RESULT_NZ(real_dim2_h);
    s_vpi_arrayvalue real_dim2_v = {vpiRealVal,0,nullptr};
    vpi_get_value_array(real_dim2_h,&real_dim2_v,index,6);
    CHECK_RESULT_NZ(real_dim2_v.value.reals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for(auto i = 0; i < 6; i++){
        CHECK_RESULT(real_dim2_v.value.reals[i],i+0.5);
    }

    return 0;
}

int _mon_check_get_rawvals(){
    // 2D vpiRawTwoStateVal VLVT_UINT8
    int index[2] = {0,0};
    TestVpiHandle rawvals_dim2_8_h = VPI_HANDLE("rawvals_dim2_8");
    CHECK_RESULT_NZ(rawvals_dim2_8_h);
    s_vpi_arrayvalue rawvals_dim2_8_v = {vpiRawTwoStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_8_h,&rawvals_dim2_8_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_8_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    const auto rawvals_dim2_8_vp = reinterpret_cast<PLI_UBYTE8*>(rawvals_dim2_8_v.value.rawvals);
    for (auto i = 0; i < 6; i++) {
        CHECK_RESULT(rawvals_dim2_8_vp[i],i);
    }

    // 2D vpiRawTwoStateVal VLVT_UINT16
    TestVpiHandle rawvals_dim2_16_h = VPI_HANDLE("rawvals_dim2_16");
    CHECK_RESULT_NZ(rawvals_dim2_16_h);
    s_vpi_arrayvalue rawvals_dim2_16_v = {vpiRawTwoStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_16_h,&rawvals_dim2_16_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_16_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    const auto rawvals_dim2_16_vp = reinterpret_cast<PLI_UBYTE8*>(rawvals_dim2_16_v.value.rawvals);
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 2; j++) {
            CHECK_RESULT(rawvals_dim2_16_vp[(2*i)+j],i+(j<<4));
        }
    }

    //2D vpiRawTwoStateVal VLVT_UINT32
    TestVpiHandle rawvals_dim2_24_h = VPI_HANDLE("rawvals_dim2_24");
    CHECK_RESULT_NZ(rawvals_dim2_24_h);
    s_vpi_arrayvalue rawvals_dim2_24_v = {vpiRawTwoStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_24_h,&rawvals_dim2_24_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_24_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    const auto rawvals_dim2_24_vp = reinterpret_cast<PLI_UBYTE8*>(rawvals_dim2_24_v.value.rawvals);
    for (auto i = 0; i < 3; i++) {
        for (auto j = 0; j < 3; j++) {
            CHECK_RESULT(rawvals_dim2_24_vp[(3*i)+j],i+(j<<4));
        }
    }

    // 2D vpiRawTwoStateVal VLVT_UINT64
    TestVpiHandle rawvals_dim2_40_h = VPI_HANDLE("rawvals_dim2_40");
    CHECK_RESULT_NZ(rawvals_dim2_40_h);
    s_vpi_arrayvalue rawvals_dim2_40_v = {vpiRawTwoStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_40_h,&rawvals_dim2_40_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_40_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    const auto rawvals_dim2_40_vp = reinterpret_cast<PLI_UBYTE8*>(rawvals_dim2_40_v.value.rawvals);
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 5; j++) {
            CHECK_RESULT(rawvals_dim2_40_vp[(5*i)+j],i+(j<<4));
        }
    }

    // 2D vpiRawTwoStateVal VLVT_WDATA
    TestVpiHandle rawvals_dim2_72_h = VPI_HANDLE("rawvals_dim2_72");
    CHECK_RESULT_NZ(rawvals_dim2_72_h);
    s_vpi_arrayvalue rawvals_dim2_72_v = {vpiRawTwoStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_72_h,&rawvals_dim2_72_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_72_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    const auto rawvals_dim2_72_vp = reinterpret_cast<PLI_UBYTE8*>(rawvals_dim2_72_v.value.rawvals);
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 9; j++) {
            CHECK_RESULT(rawvals_dim2_72_vp[(9*i)+j],i+(j<<4));
        }
    }

    // 2D vpiRawTwoStateVal VLVT_WDATA non-zero index
    index[0] = 1;
    index[1] = 1;
    rawvals_dim2_72_v = {vpiRawTwoStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_72_h,&rawvals_dim2_72_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_72_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 9; j++) {
            CHECK_RESULT(rawvals_dim2_72_vp[(9*i)+j],((i+4)%6)+(j<<4));
        }
    }

    // 2D vpiRawFourStateVal VLVT_UINT8
    index[0] = 0;
    index[1] = 0;
    rawvals_dim2_8_v = {vpiRawFourStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_8_h,&rawvals_dim2_8_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_8_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 6; i++) {
        CHECK_RESULT(rawvals_dim2_8_vp[(2*i)],i);
        CHECK_RESULT_Z(rawvals_dim2_8_vp[(2*i)+1]);
    }

    // 2D vpiRawFourStateVal VLVT_UINT16
    rawvals_dim2_16_v = {vpiRawFourStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_16_h,&rawvals_dim2_16_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_16_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 2; j++) {
            CHECK_RESULT(rawvals_dim2_16_vp[(2*((2*i)+j))],i+(j<<4));
            CHECK_RESULT_Z(rawvals_dim2_16_vp[(2*((2*i)+j))+1]);
        }
    }

    //2D vpiRawFourStateVal VLVT_UINT32
    rawvals_dim2_24_v = {vpiRawFourStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_24_h,&rawvals_dim2_24_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_24_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 3; i++) {
        for (auto j = 0; j < 3; j++) {
            CHECK_RESULT(rawvals_dim2_24_vp[(2*((3*i)+j))],i+(j<<4));
            CHECK_RESULT_Z(rawvals_dim2_24_vp[(2*((3*i)+j))+1]);
        }
    }

    // 2D vpiRawFourStateVal VLVT_UINT64
    rawvals_dim2_40_v = {vpiRawFourStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_40_h,&rawvals_dim2_40_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_40_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 5; j++) {
            CHECK_RESULT(rawvals_dim2_40_vp[(2*((5*i)+j))],i+(j<<4));
            CHECK_RESULT_Z(rawvals_dim2_40_vp[(2*((5*i)+j))+1]);
        }
    }

    // 2D vpiRawFourStateVal VLVT_WDATA
    rawvals_dim2_72_v = {vpiRawFourStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_72_h,&rawvals_dim2_72_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_72_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 9; j++) {
            CHECK_RESULT(rawvals_dim2_72_vp[(2*((9*i)+j))],i+(j<<4));
            CHECK_RESULT_Z(rawvals_dim2_72_vp[(2*((9*i)+j))+1]);
        }
    }

    // 2D vpiRawFourStateVal VLVT_WDATA non-zero index
    index[0] = 1;
    index[1] = 1;
    rawvals_dim2_72_v = {vpiRawFourStateVal,0,nullptr};
    vpi_get_value_array(rawvals_dim2_72_h,&rawvals_dim2_72_v,index,6);
    CHECK_RESULT_NZ(rawvals_dim2_72_v.value.rawvals);
    CHECK_RESULT_Z(vpi_chk_error(nullptr));
    for (auto i = 0; i < 6; i++) {
        for (auto j = 0; j < 9; j++) {
            CHECK_RESULT(rawvals_dim2_72_vp[(2*((9*i)+j))],((i+4)%6)+(j<<4));
            CHECK_RESULT_Z(rawvals_dim2_72_vp[(2*((9*i)+j))+1]);
        }
    }
    
    return 0;
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
#ifdef TEST_VERBOSE
    printf("-mon_check()\n");
#endif
    if(int status = _mon_check_get_bad()) return status;
    if(int status = _mon_check_get_int()) return status;
    if(int status = _mon_check_get_vector()) return status;
    if(int status = _mon_check_get_real()) return status;
    if(int status = _mon_check_get_rawvals()) return status;
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
