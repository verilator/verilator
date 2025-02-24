// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2024 by Wilson Snyder. This program is free software; you can
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

#include "Vt_vpi_multidim.h"
#include "Vt_vpi_multidim__Dpi.h"
#include "svdpi.h"

#endif

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <random>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;

// TEST START

void _arr_type_check(TestVpiHandle& arr_h, int expType, int expSize, int expRangeHigh,
                     int expRangeLow) {
    const int vpitype = vpi_get(vpiType, arr_h);
    TEST_CHECK_EQ(vpitype, expType);
    const int vpisize = vpi_get(vpiSize, arr_h);
    TEST_CHECK_EQ(vpisize, expSize);

    s_vpi_value value;
    value.format = vpiIntVal;

    TestVpiHandle left_h = vpi_handle(vpiLeftRange, arr_h);
    TEST_CHECK_NZ(left_h);
    vpi_get_value(left_h, &value);
    TEST_CHECK_EQ(value.value.integer, expRangeHigh);

    TestVpiHandle right_h = vpi_handle(vpiRightRange, arr_h);
    TEST_CHECK_NZ(right_h);
    vpi_get_value(right_h, &value);
    TEST_CHECK_EQ(value.value.integer, expRangeLow);
}

void _arr_iter_check(const char* name, int wordSize, const int* lows) {
    TestVpiHandle arr_h
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(TestSimulator::rooted(name)), NULL);
    TEST_CHECK_NZ(arr_h);

    _arr_type_check(arr_h, vpiRegArray, 4, lows[0] + 1, lows[0]);

    {
        // can't iterate through RegArrays on a nested RegArray
        TestVpiHandle arr_iter_h = vpi_iterate(vpiRegArray, arr_h);
        TEST_CHECK_Z(vpi_scan(arr_iter_h));
        arr_iter_h.freed();
    }

    if (!TestSimulator::is_questa()) {
        // but we can access them by index (Questa can't)
        for (int idx = lows[0]; idx < lows[0] + 2; idx++) {
            TestVpiHandle arr_elem_h = vpi_handle_by_index(arr_h, idx);
            TEST_CHECK_NZ(arr_elem_h);

            // first indexing yields size-2 RegArrays
            _arr_type_check(arr_elem_h, vpiRegArray, 2, lows[1] + 1, lows[1]);

            for (int idx2 = lows[1]; idx2 < lows[1] + 2; idx2++) {
                TestVpiHandle arr_elem2_h = vpi_handle_by_index(arr_elem_h, idx2);
                TEST_CHECK_NZ(arr_elem2_h);

                // second indexing yields wordSize Regs
                _arr_type_check(arr_elem2_h, vpiReg, wordSize, lows[2] + 1, lows[2]);
            }
        }
    }

    {
        // it's also possible to directly iterate through all four Regs
        TestVpiHandle arr_iter_h = vpi_iterate(vpiReg, arr_h);
        for (int idx = 0; idx < 4; idx++) {
            TestVpiHandle arr_elem_h = vpi_scan(arr_iter_h);
            TEST_CHECK_NZ(arr_elem_h);

            // which gives us wordSize Regs
            _arr_type_check(arr_elem_h, vpiReg, wordSize, lows[2] + 1, lows[2]);

            {
                // can't iterate through Regs on a nested Reg
                TestVpiHandle arr_iter2_h = vpi_iterate(vpiReg, arr_elem_h);
                TEST_CHECK_Z(vpi_scan(arr_iter2_h));
                arr_iter2_h.freed();
            }

            // but we can access them by index
            for (int idx2 = lows[2]; idx2 < lows[2] + 2; idx2++) {
                TestVpiHandle arr_elem2_h = vpi_handle_by_index(arr_elem_h, idx2);
                TEST_CHECK_NZ(arr_elem2_h);

                // first indexing yields wordSize / 2 Regs
                _arr_type_check(arr_elem2_h, vpiReg, wordSize / 2, lows[3] + wordSize / 2 - 1,
                                lows[3]);

                for (int idx3 = lows[3]; idx3 < lows[3] + wordSize / 2; idx3++) {
                    TestVpiHandle arr_elem3_h = vpi_handle_by_index(arr_elem2_h, idx3);
                    TEST_CHECK_NZ(arr_elem3_h);
                    {
                        // second indexing yields size-1 RegBits (no support for RegBit VPI type
                        // yet)
                        const int vpitype = vpi_get(vpiType, arr_elem3_h);
                        if (TestSimulator::is_verilator()) {
                            TEST_CHECK_EQ(vpitype, vpiReg);
                        } else {
                            TEST_CHECK_EQ(vpitype, vpiRegBit);
                        }
                        const int vpisize = vpi_get(vpiSize, arr_elem3_h);
                        TEST_CHECK_EQ(vpisize, 1);
                    }
                }
            }

            // iterating through packed ranges
            TestVpiHandle range_iter_h = vpi_iterate(vpiRange, arr_elem_h);
            for (int idx2 = 0; idx2 < 2; idx2++) {
                TestVpiHandle range_h = vpi_scan(range_iter_h);
                TEST_CHECK_NZ(range_h);
                {
                    s_vpi_value value;
                    value.format = vpiIntVal;
                    TestVpiHandle side_h = vpi_handle(vpiLeftRange, range_h);
                    TEST_CHECK_NZ(side_h);
                    vpi_get_value(side_h, &value);
                    if (idx2 == 0) {
                        TEST_CHECK_EQ(value.value.integer, lows[2] + 1);
                    } else {
                        TEST_CHECK_EQ(value.value.integer, lows[3] + wordSize / 2 - 1);
                    }
                    side_h = vpi_handle(vpiRightRange, range_h);
                    TEST_CHECK_NZ(side_h);
                    vpi_get_value(side_h, &value);
                    if (idx2 == 0) {
                        TEST_CHECK_EQ(value.value.integer, lows[2]);
                    } else {
                        TEST_CHECK_EQ(value.value.integer, lows[3]);
                    }
                }
            }
            TEST_CHECK_Z(vpi_scan(range_iter_h));
            range_iter_h.freed();
        }
        TEST_CHECK_Z(vpi_scan(arr_iter_h));
        arr_iter_h.freed();
    }

    {
        // iterating through unpacked ranges
        TestVpiHandle range_iter_h = vpi_iterate(vpiRange, arr_h);
        for (int idx = 0; idx < 2; idx++) {
            TestVpiHandle range_h = vpi_scan(range_iter_h);
            TEST_CHECK_NZ(range_h);
            {
                s_vpi_value value;
                value.format = vpiIntVal;
                TestVpiHandle side_h = vpi_handle(vpiLeftRange, range_h);
                TEST_CHECK_NZ(side_h);
                vpi_get_value(side_h, &value);
                if (idx == 0) {
                    TEST_CHECK_EQ(value.value.integer, lows[0] + 1);
                } else {
                    TEST_CHECK_EQ(value.value.integer, lows[1] + 1);
                }
                side_h = vpi_handle(vpiRightRange, range_h);
                TEST_CHECK_NZ(side_h);
                vpi_get_value(side_h, &value);
                if (idx == 0) {
                    TEST_CHECK_EQ(value.value.integer, lows[0]);
                } else {
                    TEST_CHECK_EQ(value.value.integer, lows[1]);
                }
            }
        }
        TEST_CHECK_Z(vpi_scan(range_iter_h));
        range_iter_h.freed();
    }
}

void _arr_access_format_check(TestVpiHandle& reg_h, int wordSize, const int* lows,
                              const char* octVal_s, PLI_INT32 format) {
    const int spanSize = wordSize / 2;
    s_vpi_value value_in;
    s_vpi_value value_out;
    s_vpi_error_info e;
    char zero_s[2] = "0";

    // zero out the vector
    value_in.format = vpiOctStrVal;
    value_in.value.str = zero_s;
    vpi_put_value(reg_h, &value_in, NULL, vpiNoDelay);
    TEST_CHECK_Z(vpi_chk_error(&e));

    value_in.format = format;
    value_out.format = format;

    for (int i = 0; i < 2; i++) {
        TestVpiHandle subreg_h = vpi_handle_by_index(reg_h, lows[2] + i);
        TEST_CHECK_NZ(subreg_h);

        char octSpan_s[spanSize / 3 + 1];
        strncpy(octSpan_s, &octVal_s[spanSize / 3 * (1 - i)], spanSize / 3);
        octSpan_s[spanSize / 3] = '\0';

        uint64_t intVal;
        t_vpi_vecval vecVal[2];
        sscanf(octSpan_s, "%" SCNo64, &intVal);
        char strVal_s[spanSize + 1];  // max length of the string happens for binary

        if (format == vpiIntVal) {
            value_in.value.integer = intVal;
        } else if (format == vpiVectorVal) {
            if (spanSize > 32) {
                vecVal[1].aval = intVal >> 32;
                vecVal[1].bval = 0;
            }
            vecVal[0].aval = intVal;
            vecVal[0].bval = 0;
            value_in.value.vector = vecVal;
        } else if (format == vpiBinStrVal) {
            for (int j = 0; j < spanSize; j++)
                strVal_s[j] = (intVal >> (spanSize - j - 1)) % 2 + '0';
            strVal_s[spanSize] = '\0';
            value_in.value.str = strVal_s;
        } else if (format == vpiDecStrVal) {
            sprintf(strVal_s, "%" PRIu64, intVal);
            value_in.value.str = strVal_s;
        } else if (format == vpiHexStrVal) {
            sprintf(strVal_s, "%0*" PRIx64, (spanSize + 3) / 4, intVal);
            value_in.value.str = strVal_s;
        } else if (format == vpiOctStrVal) {
            sprintf(strVal_s, "%" PRIo64, intVal);
            value_in.value.str = strVal_s;
        } else if (format == vpiStringVal) {
            const int byteCount = (spanSize + 7) / 8;
            for (int j = 0; j < byteCount; j++)
                strVal_s[j] = (intVal >> (8 * (byteCount - j - 1))) & 0xff;
            strVal_s[byteCount] = '\0';
            value_in.value.str = strVal_s;
        }

        vpi_put_value(subreg_h, &value_in, NULL, vpiNoDelay);
        TEST_CHECK_Z(vpi_chk_error(&e));

        vpi_get_value(subreg_h, &value_out);
        switch (format) {
        case vpiIntVal: TEST_CHECK_EQ(value_out.value.integer, value_in.value.integer); break;
        case vpiVectorVal:
            if (spanSize > 32)
                TEST_CHECK_EQ(value_out.value.vector[1].aval, value_in.value.vector[1].aval);
            TEST_CHECK_EQ(value_out.value.vector[0].aval, value_in.value.vector[0].aval);
            break;
        case vpiStringVal:
            TEST_CHECK_EQ(value_out.value.str[0],
                          value_in.value.str[0] ? value_in.value.str[0] : ' ');
            break;
        case vpiBinStrVal:
        case vpiDecStrVal:
        case vpiHexStrVal:
        case vpiOctStrVal: TEST_CHECK_CSTR(value_out.value.str, value_in.value.str); break;
        }
    }

    // validate the resulting flattened vector
    value_out.format = vpiOctStrVal;
    vpi_get_value(reg_h, &value_out);
    TEST_CHECK_CSTR(value_out.value.str, octVal_s);
}

std::default_random_engine rng;

void _arr_access_check(const char* name, int wordSize, const int* lows) {
    TestVpiHandle arr_h
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(TestSimulator::rooted(name)), NULL);
    TEST_CHECK_NZ(arr_h);

    std::uniform_int_distribution<uint64_t> rand64(std::numeric_limits<uint64_t>::min(),
                                                   std::numeric_limits<uint64_t>::max());

    char octVal_s[wordSize / 3 + 1];

    // fill octVal_s with random octal digits
    if (wordSize < 64) {
        sprintf(octVal_s, "%0*" PRIo64, wordSize / 3,
                rand64(rng) % (static_cast<uint64_t>(1) << wordSize));
    } else {
        sprintf(octVal_s, "%0*" PRIo64, 63 / 3, rand64(rng));
        sprintf(octVal_s + 63 / 3, "%0*" PRIo64, (wordSize - 63) / 3,
                rand64(rng) % (static_cast<uint64_t>(1) << (wordSize - 63)));
    }

    // Assume that reading/writing to the "flattened" packed register is already tested,
    // check only reading/writing to sub-regs and validate the flattened result.
    {
        TestVpiHandle arr_iter_h = vpi_iterate(vpiReg, arr_h);
        while (TestVpiHandle reg_h = vpi_scan(arr_iter_h)) {
            s_vpi_value value_in;
            s_vpi_value value_out;
            s_vpi_error_info e;

            value_out.format = vpiOctStrVal;
            value_in.format = vpiOctStrVal;
            value_in.value.str = octVal_s;
            vpi_put_value(reg_h, &value_in, NULL, vpiNoDelay);
            TEST_CHECK_Z(vpi_chk_error(&e));
            vpi_get_value(reg_h, &value_out);
            TEST_CHECK_CSTR(value_out.value.str, octVal_s);

            // test each I/O data format
            if (wordSize <= 64) {
                _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiIntVal);
                _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiDecStrVal);
            }
            _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiVectorVal);
            _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiBinStrVal);
            _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiOctStrVal);
            _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiHexStrVal);
            _arr_access_format_check(reg_h, wordSize, lows, octVal_s, vpiStringVal);
        }
        arr_iter_h.freed();
    }
}

struct params {
    const char* name;
    int wordSize;
    const int lows[4];
};

void _multidim_check() {
    static struct params values[]
        = {{"arr_cdata", 6, {0, 1, 2, 3}},       {"arr_sdata", 12, {4, 5, 6, 7}},
           {"arr_idata", 30, {8, 9, 10, 11}},    {"arr_qdata", 60, {12, 13, 14, 15}},
           {"arr_wdata", 126, {16, 17, 18, 19}}, {nullptr, 0, {0, 0, 0, 0}}};
    struct params* value = values;
    while (value->name) {
        _arr_iter_check(value->name, value->wordSize, value->lows);
        _arr_access_check(value->name, value->wordSize, value->lows);
        value++;
    }
}

// TEST END

extern "C" int mon_check() {
    // Callback from initial block in monitor
    //if (int status = _mon_check_param()) return status;
    printf("-mon_check()\n");
    _multidim_check();
    return errors;
}

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

void vpi_compat_bootstrap(void) {
    p_vpi_systf_data systf_data_p;
    systf_data_p = &(vpi_systf_data[0]);
    while (systf_data_p->type != 0) vpi_register_systf(systf_data_p++);
}

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;  // TODO
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
    contextp->timeInc(10);

    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        contextp->timeInc(1);
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
