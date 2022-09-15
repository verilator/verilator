// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = nullptr;
bool pass = true;

double sc_time_stamp() { return 0; }

void compare_signals(const sc_signal<sc_bv<256>>& ls, const sc_signal<sc_bv<256>>& rs) {
    if (ls.read() != rs.read()) {
        pass &= false;
        VL_PRINTF("%%Error: Data missmatch in signals %s and %s\n", ls.name(), rs.name());
    }
}

void compareWls(int obits, WDataInP const lwp, WDataInP const rwp) {
    const int words = VL_WORDS_I(obits);
    bool same = true;

    for (int i = 0; (i < (words - 1)); ++i) {
        if (lwp[i] != rwp[i]) { same = false; }
    }
    if ((lwp[words - 1] & VL_MASK_E(obits)) != (rwp[words - 1] & VL_MASK_E(obits))) {
        same = false;
    }

    if (!same) {
        pass &= false;
        VL_PRINTF("%%Error: There is a difference in VlWide variable %d bits wide\n", obits);
    }
}

// old macro which is correct but has MT issue with range
#define VL_ASSIGN_SBW_MT_ISSUE(obits, svar, rwp) \
    { \
        sc_biguint<(obits)> _butemp; \
        for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
            int msb = ((i + 1) * VL_IDATASIZE) - 1; \
            msb = (msb >= (obits)) ? ((obits)-1) : msb; \
            _butemp.range(msb, i* VL_IDATASIZE) = (rwp)[i]; \
        } \
        (svar).write(_butemp); \
    }

#ifdef SYSTEMC_VERSION
int sc_main(int, char**)
#else
int main()
#endif
{
    Verilated::debug(0);
    tb = new VM_PREFIX("tb");

    VlWide<8> /*255:0*/ input_var;
    VlWide<8> /*255:0*/ out_var;

    // msb is always set to F not to be false positive on checking equality
    input_var.m_storage[0] = 0xF2341234;
    input_var.m_storage[1] = 0xFEADBEEF;
    input_var.m_storage[2] = 0xF5A5A5A5;
    input_var.m_storage[3] = 0xF1B2C3D4;
    input_var.m_storage[4] = 0xFFFFFFFF;
    input_var.m_storage[5] = 0xFAAABBBB;
    input_var.m_storage[6] = 0xF000AAAA;
    input_var.m_storage[7] = 0xF0101010;

#ifdef SYSTEMC_VERSION
    // clang-format off
    sc_signal<sc_bv<256>> SC_NAMED(i_29_s), SC_NAMED(i_29_old_s), SC_NAMED(o_29_s), SC_NAMED(o_29_old_s),
                          SC_NAMED(i_30_s), SC_NAMED(i_30_old_s), SC_NAMED(o_30_s), SC_NAMED(o_30_old_s),
                          SC_NAMED(i_31_s), SC_NAMED(i_31_old_s), SC_NAMED(o_31_s), SC_NAMED(o_31_old_s),
                          SC_NAMED(i_32_s), SC_NAMED(i_32_old_s), SC_NAMED(o_32_s), SC_NAMED(o_32_old_s),
                          SC_NAMED(i_59_s), SC_NAMED(i_59_old_s), SC_NAMED(o_59_s), SC_NAMED(o_59_old_s),
                          SC_NAMED(i_60_s), SC_NAMED(i_60_old_s), SC_NAMED(o_60_s), SC_NAMED(o_60_old_s),
                          SC_NAMED(i_62_s), SC_NAMED(i_62_old_s), SC_NAMED(o_62_s), SC_NAMED(o_62_old_s),
                          SC_NAMED(i_64_s), SC_NAMED(i_64_old_s), SC_NAMED(o_64_s), SC_NAMED(o_64_old_s),
                          SC_NAMED(i_119_s), SC_NAMED(i_119_old_s), SC_NAMED(o_119_s), SC_NAMED(o_119_old_s),
                          SC_NAMED(i_120_s), SC_NAMED(i_120_old_s), SC_NAMED(o_120_s), SC_NAMED(o_120_old_s),
                          SC_NAMED(i_121_s), SC_NAMED(i_121_old_s), SC_NAMED(o_121_s), SC_NAMED(o_121_old_s),
                          SC_NAMED(i_127_s), SC_NAMED(i_127_old_s), SC_NAMED(o_127_s), SC_NAMED(o_127_old_s),
                          SC_NAMED(i_128_s), SC_NAMED(i_128_old_s), SC_NAMED(o_128_s), SC_NAMED(o_128_old_s),
                          SC_NAMED(i_255_s), SC_NAMED(i_255_old_s), SC_NAMED(o_255_s), SC_NAMED(o_255_old_s),
                          SC_NAMED(i_256_s), SC_NAMED(i_256_old_s), SC_NAMED(o_256_s), SC_NAMED(o_256_old_s);


    tb->i_29(i_29_s); tb->i_29_old(i_29_old_s); tb->o_29(o_29_s); tb->o_29_old(o_29_old_s);
    tb->i_30(i_30_s); tb->i_30_old(i_30_old_s); tb->o_30(o_30_s); tb->o_30_old(o_30_old_s);
    tb->i_31(i_31_s); tb->i_31_old(i_31_old_s); tb->o_31(o_31_s); tb->o_31_old(o_31_old_s);
    tb->i_32(i_32_s); tb->i_32_old(i_32_old_s); tb->o_32(o_32_s); tb->o_32_old(o_32_old_s);
    tb->i_59(i_59_s); tb->i_59_old(i_59_old_s); tb->o_59(o_59_s); tb->o_59_old(o_59_old_s);
    tb->i_60(i_60_s); tb->i_60_old(i_60_old_s); tb->o_60(o_60_s); tb->o_60_old(o_60_old_s);
    tb->i_62(i_62_s); tb->i_62_old(i_62_old_s); tb->o_62(o_62_s); tb->o_62_old(o_62_old_s);
    tb->i_64(i_64_s); tb->i_64_old(i_64_old_s); tb->o_64(o_64_s); tb->o_64_old(o_64_old_s);
    tb->i_119(i_119_s); tb->i_119_old(i_119_old_s); tb->o_119(o_119_s); tb->o_119_old(o_119_old_s);
    tb->i_120(i_120_s); tb->i_120_old(i_120_old_s); tb->o_120(o_120_s); tb->o_120_old(o_120_old_s);
    tb->i_121(i_121_s); tb->i_121_old(i_121_old_s); tb->o_121(o_121_s); tb->o_121_old(o_121_old_s);
    tb->i_127(i_127_s); tb->i_127_old(i_127_old_s); tb->o_127(o_127_s); tb->o_127_old(o_127_old_s);
    tb->i_128(i_128_s); tb->i_128_old(i_128_old_s); tb->o_128(o_128_s); tb->o_128_old(o_128_old_s);
    tb->i_255(i_255_s); tb->i_255_old(i_255_old_s); tb->o_255(o_255_s); tb->o_255_old(o_255_old_s);
    tb->i_256(i_256_s); tb->i_256_old(i_256_old_s); tb->o_256(o_256_s); tb->o_256_old(o_256_old_s);

    // clang-format on

#endif

// clang-format off
#ifdef SYSTEMC_VERSION
    sc_start(1, SC_NS);
#else
    tb->eval();
#endif
    // This testcase is testing multi-thread safe VL_ASSIGN_SBW and VL_ASSIGN_WSB macros.
    // Testbench is assigning different number of bits from VlWide input_var variable to different inputs.
    // Values around multiple of 30 (i.e. BITS_PER_DIGIT defined in SystemC sc_nbdefs.h) are tested with the special care, since
    // it is the value by which the data_ptr of sc_biguint underlying data type is increased by (and not expected 32, as width of uint32_t).
    // Correctness of the output is compared against the 'old' macro, which is correct but has multi-threaded issue since it's using range function.
    // Second part is testing VL_ASSIGN_WSB in a reverse way, it is reading signals from the previous test,
    // and comparing the output with (fraction) of VlWide input_var variable.

    // clang-format on
    VL_ASSIGN_SBW(29, i_29_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(29, i_29_old_s, input_var);
    VL_ASSIGN_SBW(30, i_30_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(30, i_30_old_s, input_var);
    VL_ASSIGN_SBW(31, i_31_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(31, i_31_old_s, input_var);
    VL_ASSIGN_SBW(32, i_32_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(32, i_32_old_s, input_var);
    VL_ASSIGN_SBW(59, i_59_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(59, i_59_old_s, input_var);
    VL_ASSIGN_SBW(60, i_60_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(60, i_60_old_s, input_var);
    VL_ASSIGN_SBW(62, i_62_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(62, i_62_old_s, input_var);
    VL_ASSIGN_SBW(64, i_64_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(64, i_64_old_s, input_var);
    VL_ASSIGN_SBW(119, i_119_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(119, i_119_old_s, input_var);
    VL_ASSIGN_SBW(120, i_120_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(120, i_120_old_s, input_var);
    VL_ASSIGN_SBW(121, i_121_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(121, i_121_old_s, input_var);
    VL_ASSIGN_SBW(127, i_127_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(127, i_127_old_s, input_var);
    VL_ASSIGN_SBW(128, i_128_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(128, i_128_old_s, input_var);
    VL_ASSIGN_SBW(255, i_255_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(255, i_255_old_s, input_var);
    VL_ASSIGN_SBW(256, i_256_s, input_var);
    VL_ASSIGN_SBW_MT_ISSUE(256, i_256_old_s, input_var);

#ifdef SYSTEMC_VERSION
    sc_start(1, SC_NS);
#else
    tb->eval();
#endif
    compare_signals(o_29_s, o_29_old_s);
    compare_signals(o_30_s, o_30_old_s);
    compare_signals(o_31_s, o_31_old_s);
    compare_signals(o_32_s, o_32_old_s);
    compare_signals(o_59_s, o_59_old_s);
    compare_signals(o_60_s, o_60_old_s);
    compare_signals(o_62_s, o_62_old_s);
    compare_signals(o_64_s, o_64_old_s);
    compare_signals(o_119_s, o_119_old_s);
    compare_signals(o_120_s, o_120_old_s);
    compare_signals(o_121_s, o_121_old_s);
    compare_signals(o_127_s, o_127_old_s);
    compare_signals(o_128_s, o_128_old_s);
    compare_signals(o_255_s, o_255_old_s);
    compare_signals(o_256_s, o_256_old_s);

    ////////////////////////////////

    VL_ASSIGN_WSB(29, out_var, o_29_s);
    compareWls(29, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(30, out_var, o_30_s);
    compareWls(30, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(31, out_var, o_31_s);
    compareWls(31, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(32, out_var, o_32_s);
    compareWls(32, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(59, out_var, o_59_s);
    compareWls(59, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(60, out_var, o_60_s);
    compareWls(60, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(62, out_var, o_62_s);
    compareWls(62, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(64, out_var, o_64_s);
    compareWls(64, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(119, out_var, o_119_s);
    compareWls(119, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(120, out_var, o_120_s);
    compareWls(120, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(121, out_var, o_121_s);
    compareWls(121, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(127, out_var, o_127_s);
    compareWls(127, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(128, out_var, o_128_s);
    compareWls(128, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(255, out_var, o_255_s);
    compareWls(255, input_var.data(), out_var.data());
    VL_ASSIGN_WSB(256, out_var, o_256_s);
    compareWls(256, input_var.data(), out_var.data());

    tb->final();
    VL_DO_DANGLING(delete tb, tb);

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from test\n");
    }
    return 0;
}
