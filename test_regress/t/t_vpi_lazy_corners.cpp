// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE
#include "vpi_user.h"

#include <cstdio>
#include <cstring>
#include <memory>

namespace {

int errors = 0;

vpiHandle mustFind(const char* name) {
    vpiHandle handle = vpi_handle_by_name((PLI_BYTE8*)name, nullptr);
    if (!handle) {
        std::printf("%%Error: failed to find %s\n", name);
        ++errors;
    }
    return handle;
}

int readInt(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return value.value.integer;
}

void checkInt(const char* name, vpiHandle handle, int expected) {
    const int got = readInt(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, got);
        ++errors;
    }
}

void checkReal(const char* name, vpiHandle handle, double expected) {
    s_vpi_value value{};
    value.format = vpiRealVal;
    vpi_get_value(handle, &value);
    if (value.value.real != expected) {
        std::printf("%%Error: %s expected %g, got %g\n", name, expected, value.value.real);
        ++errors;
    }
}

void checkString(const char* name, vpiHandle handle, const char* expected) {
    s_vpi_value value{};
    value.format = vpiStringVal;
    vpi_get_value(handle, &value);
    if (std::strcmp(value.value.str, expected) != 0) {
        std::printf("%%Error: %s expected '%s', got '%s'\n", name, expected, value.value.str);
        ++errors;
    }
}

// Walk a two-dimensional unpacked array by index value, lowest first in each dimension: a
// descending range declares the same set of indices as the ascending one.
// 'mask' limits the first element, whose high byte the gap case leaves undriven.
void checkElems(const char* name, vpiHandle arrayp, int outerLo, int outerN, int innerLo,
                int innerN, const int* expected, int mask = -1) {
    for (int i = 0; i < outerN; ++i) {
        vpiHandle rowp = vpi_handle_by_index(arrayp, outerLo + i);
        if (!rowp) {
            std::printf("%%Error: failed to index %s[%0d]\n", name, outerLo + i);
            ++errors;
            continue;
        }
        for (int j = 0; j < innerN; ++j) {
            vpiHandle elemp = vpi_handle_by_index(rowp, innerLo + j);
            if (!elemp) {
                std::printf("%%Error: failed to index %s[%0d][%0d]\n", name, outerLo + i,
                            innerLo + j);
                ++errors;
                continue;
            }
            const int m = (i || j) ? -1 : mask;
            const int got = readInt(elemp) & m;
            const int want = expected[i * innerN + j] & m;
            if (got != want) {
                std::printf("%%Error: %s[%0d][%0d] expected %0d, got %0d\n", name, outerLo + i,
                            innerLo + j, want, got);
                ++errors;
            }
        }
    }
}

void putInt(vpiHandle handle, int v) {
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = v;
    if (!vpi_put_value(handle, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value failed\n");
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    topp->a = 0;
    topp->b = 0;
    topp->sel = 0;
    topp->frc2_force = 0;
    topp->data = 0;
    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    // iopartial
    {
        vpiHandle outh = mustFind("out");
        if (errors) return 10;
        int keep = 0;
        const auto outOf = [](int k) { return (k & 0xf) | (((k >> 4) ^ 0xf) << 4); };
        for (int i = 0; i < 5; ++i) {
            cycle();
            keep = (keep + 0x11) & 0xff;
            checkInt("out", outh, outOf(keep));
        }
    }

    // dtypes
    {
        topp->a = 0x3c;  // in0 == 0x3c == 60
        cycle();
        const int in0 = 0x3c;
        checkReal("t.r_comb", mustFind("t.r_comb"), 1.5);
        checkInt("t.i_comb", mustFind("t.i_comb"), in0 + 1);
        checkInt("t.en_comb", mustFind("t.en_comb"), in0 & 0x3);
        checkString("t.s_var", mustFind("t.s_var"), "hi");
        checkInt("t.v_comb", mustFind("t.v_comb"), (in0 ^ 0x5) & 0x7f);
        checkString("t.s_fmt", mustFind("t.s_fmt"), "v60");
        checkInt("t.ps_comb", mustFind("t.ps_comb"), in0);
        const int paFlat = ((in0 & 0xff) << 24) | (((in0 ^ 0xff) & 0xff) << 16)
                           | (((in0 + 1) & 0xff) << 8) | ((in0 - 1) & 0xff);
        checkInt("t.pa_comb", mustFind("t.pa_comb"), paFlat);
        {
            vpiHandle pah = mustFind("t.pa_comb");
            vpiHandle e0 = vpi_handle_by_index(pah, 0);
            if (!e0) {
                std::printf("%%Error: failed to index t.pa_comb[0]\n");
                ++errors;
            } else {
                checkInt("t.pa_comb[0]", e0, (in0 - 1) & 0xff);
            }
        }
        checkInt("t.mem", mustFind("t.mem"), in0);  // element 0
        checkInt("t.mem_part", mustFind("t.mem_part"), in0 ^ 0x27);  // element 0

        // mdcover: every element of the fully covered array reads back, addressed by its
        // declared index in each direction; the sliced element assembles from both writes
        {
            const int full[3][2] = {{((~in0 & 0xff) << 8) | in0, (in0 << 8) | 0x11},
                                    {(in0 << 8) | 0x22, (in0 << 8) | 0x33},
                                    {(in0 << 8) | 0x44, (in0 << 8) | 0x55}};
            checkElems("t.md_full", mustFind("t.md_full"), 1, 3, 0, 2, &full[0][0]);
            // The gapped array is retained, so its driven elements read from storage
            const int gap[2][3] = {{in0, (in0 << 8) | 0x11, (in0 << 8) | 0x22},
                                   {(in0 << 8) | 0x33, (in0 << 8) | 0x44, (in0 << 8) | 0x55}};
            checkElems("t.md_gap", mustFind("t.md_gap"), 0, 2, 0, 3, &gap[0][0], 0xff);
        }
        mustFind("t.us_comb");

        // realcopy: a real or string row reached through a copy or a fold reads its value,
        // not the zero bytes a memcpy descriptor would leave behind
        checkReal("t.rc_alias", mustFind("t.rc_alias"), in0 + 0.5);
        checkString("t.sc_alias", mustFind("t.sc_alias"), "even");
        checkReal("t.rf_mid", mustFind("t.rf_mid"), 1.5);
        checkString("t.sf_mid", mustFind("t.sf_mid"), "hi");

        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x7;
        vpiHandle vComb = mustFind("t.v_comb");
        if (!vpi_put_value(vComb, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on reconstructed t.v_comb failed\n");
            ++errors;
        }
        checkInt("t.v_comb (deposit)", vComb, 0x7);
        if (!vpi_put_value(mustFind("t.ps_comb"), &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on reconstructed t.ps_comb failed\n");
            ++errors;
        }

        s_vpi_value uw{};
        uw.format = vpiIntVal;
        uw.value.integer = 0x5a;
        vpiHandle mem0 = vpi_handle_by_index(mustFind("t.mem"), 0);
        if (!mem0 || !vpi_put_value(mem0, &uw, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on retained t.mem[0] failed\n");
            ++errors;
        } else {
            checkInt("t.mem[0] (after write)", mem0, 0x5a);
        }
        vpiHandle usa = vpi_handle_by_name((PLI_BYTE8*)"t.us_comb.a", nullptr);
        if (!usa || !vpi_put_value(usa, &uw, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on retained t.us_comb.a failed\n");
            ++errors;
        } else {
            checkInt("t.us_comb.a (after write)", usa, 0x5a);
        }
    }

    // An explicit public_flat_rd is pinned so a cone can read it, but stays read-only: the
    // runtime write gate refuses the deposit and its value is untouched.
    {
        cycle();
        vpiHandle rdpinh = mustFind("t.rdpin");
        if (errors) return 10;
        const int pre = readInt(rdpinh);
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = (pre ^ 0xff) & 0xff;
        contextp->fatalOnVpiError(false);  // The refusal is the expected outcome here
        if (vpi_put_value(rdpinh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on public_flat_rd t.rdpin was accepted\n");
            ++errors;
        }
        t_vpi_error_info info{};
        if (!vpi_chk_error(&info)) {
            std::printf("%%Error: refused deposit into t.rdpin reported no VPI error\n");
            ++errors;
        }
        checkInt("t.rdpin (unchanged by refused put)", rdpinh, pre);
        contextp->fatalOnVpiError(true);
    }

    // dimcap
    {
        vpiHandle ctrh = mustFind("t.ctr");
        vpiHandle wideh = mustFind("t.wide");
        vpiHandle narrowh = mustFind("t.narrow");
        if (errors) return 10;
        for (int i = 0; i < 4; ++i) {
            cycle();
            const int ctr = readInt(ctrh);
            const int expectWide = ((ctr & 0xff) << 8) | (~ctr & 0xff);
            checkInt("t.wide", wideh, expectWide);
            checkInt("t.narrow", narrowh, (ctr + 1) & 0xff);
        }
    }

    // chandle
    {
        for (int i = 0; i < 4; ++i) cycle();
        vpiHandle handleh = mustFind("t.handle");
        if (errors) return 10;
        Verilated::fatalOnVpiError(false);
        s_vpi_value rd{};
        rd.format = vpiIntVal;
        vpi_get_value(handleh, &rd);
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x1;
        vpi_put_value(handleh, &wr, nullptr, vpiNoDelay);
        Verilated::fatalOnVpiError(true);
    }

    // floor
    {
        topp->a = 0x5;
        cycle();
        vpiHandle reconh = mustFind("t.recon");
        vpiHandle orphanh = mustFind("t.orphan");
        if (errors) return 10;
        checkInt("t.recon", reconh, 6);

        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x11;
        if (!vpi_put_value(reconh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on reconstructed t.recon failed\n");
            ++errors;
        }
        checkInt("t.recon (deposit)", reconh, 0x11);
        topp->eval();
        checkInt("t.recon (after eval)", reconh, 6);

        wr.value.integer = 0x2a;
        if (!vpi_put_value(orphanh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write floor-retained t.orphan\n");
            ++errors;
        }
        checkInt("t.orphan (after put)", orphanh, 0x2a);
        topp->eval();
        checkInt("t.orphan (after eval)", orphanh, 0x2a);
    }

    // multidriven
    {
        topp->a = 0x5a;
        topp->b = 0x33;
        topp->eval();
        vpiHandle wh = mustFind("t.w");
        vpiHandle rh = mustFind("t.r");
        if (errors) return 10;
        checkInt("t.w", wh, topp->b);
        checkInt("t.r", rh, topp->a & topp->b);

        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x11;
        if (!vpi_put_value(wh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write retained t.w\n");
            ++errors;
        }
        checkInt("t.w (after put)", wh, 0x11);

        wr.value.integer = 0x22;
        if (!vpi_put_value(rh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpi_put_value on reconstructed t.r failed\n");
            ++errors;
        }
        checkInt("t.r (deposit)", rh, 0x22);
        topp->eval();
        checkInt("t.w (after eval)", wh, topp->b);
        checkInt("t.r (after eval)", rh, topp->a & topp->b);
    }

    // forceable
    {
        topp->a = 0;
        topp->b = 0;
        topp->rst = 1;
        topp->clk = 0;
        topp->eval();
        cycle();
        topp->rst = 0;

        vpiHandle keeph = mustFind("t.keep_frc");
        vpiHandle frch = mustFind("t.frc");
        vpiHandle frc2h = mustFind("t.frc2");
        if (errors) return 10;

        int keep = 0;
        const auto frcOf = [](int k) { return (k + 0x11) & 0x7f; };
        const auto frc2Of = [](int k) { return (k + 0x22) & 0x7f; };

        for (int i = 0; i < 3; ++i) {
            cycle();
            keep = (keep + 0x3) & 0x7f;
            checkInt("t.keep_frc", keeph, keep);
            checkInt("t.frc", frch, frcOf(keep));
            checkInt("t.frc2", frc2h, frc2Of(keep));
        }

        topp->frc2_force = 1;
        for (int i = 0; i < 2; ++i) {
            cycle();
            keep = (keep + 0x3) & 0x7f;
            checkInt("t.keep_frc (while frc2 forced)", keeph, keep);
            checkInt("t.frc2 (while forced)", frc2h, 0x55);
        }

        topp->frc2_force = 0;
        cycle();
        keep = (keep + 0x3) & 0x7f;
        checkInt("t.keep_frc (after frc2 release)", keeph, keep);
        checkInt("t.frc2 (after release)", frc2h, frc2Of(keep));

        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x55;
        if (!vpi_put_value(frch, &wr, nullptr, vpiForceFlag)) {
            std::printf("%%Error: failed to force forceable signal t.frc\n");
            ++errors;
        }
        checkInt("t.frc (forced, pre-eval)", frch, 0x55);

        for (int i = 0; i < 2; ++i) {
            cycle();
            keep = (keep + 0x3) & 0x7f;
            checkInt("t.keep_frc (while forced)", keeph, keep);
            checkInt("t.frc (while forced)", frch, 0x55);
        }

        if (!vpi_put_value(frch, &wr, nullptr, vpiReleaseFlag)) {
            std::printf("%%Error: failed to release forceable signal t.frc\n");
            ++errors;
        }
        cycle();
        keep = (keep + 0x3) & 0x7f;
        checkInt("t.keep_frc (after release)", keeph, keep);
        checkInt("t.frc (after release)", frch, frcOf(keep));
    }

    // impureidx: impure bit-select index target retained
    {
        topp->data = 0x5;
        topp->eval();
        vpiHandle vecHnd = mustFind("t.vec");
        vpiHandle obsHnd = mustFind("t.obs_impureidx");
        if (errors) return 10;

        const int vecVal = readInt(vecHnd);
        const int obsVal = readInt(obsHnd);
        if (vecVal != obsVal) {
            std::printf("%%Error: t.vec (%0d) != t.obs_impureidx (%0d)\n", vecVal, obsVal);
            ++errors;
        }
        putInt(vecHnd, 0x5a);
        checkInt("t.vec (after put)", vecHnd, 0x5a);
    }

    // copyalias: reads track the flop across evals, and a deposit stays in the alias's own
    // shadow - it must not reach the canonical, and the next eval must discard it
    {
        vpiHandle srcHnd = mustFind("t.cpy_src");
        vpiHandle aliasHnd = mustFind("t.cpy_alias");
        if (errors) return 10;

        topp->a = 0x11;
        cycle();
        checkInt("t.cpy_alias (tracks flop)", aliasHnd, readInt(srcHnd));
        topp->a = 0x22;
        cycle();
        checkInt("t.cpy_alias (tracks flop again)", aliasHnd, readInt(srcHnd));

        const int srcBefore = readInt(srcHnd);
        putInt(aliasHnd, 0x7e);
        checkInt("t.cpy_alias (after put)", aliasHnd, 0x7e);
        checkInt("t.cpy_src (undisturbed by alias put)", srcHnd, srcBefore);
        cycle();
        checkInt("t.cpy_alias (deposit discarded)", aliasHnd, readInt(srcHnd));
    }

    // foldcopy: the folded row refreshes through the source cone's func, and a deposit stays in
    // its own shadow rather than reaching the cone it copies
    {
        vpiHandle srcHnd = mustFind("t.fold_src");
        vpiHandle midHnd = mustFind("t.fold_mid");
        if (errors) return 10;

        topp->a = 0x41;
        topp->eval();
        checkInt("t.fold_src", srcHnd, 0x41 ^ 0x3c);
        checkInt("t.fold_mid (folded copy)", midHnd, 0x41 ^ 0x3c);
        topp->a = 0x18;
        topp->eval();
        checkInt("t.fold_mid (after re-eval)", midHnd, 0x18 ^ 0x3c);

        putInt(midHnd, 0x99);
        checkInt("t.fold_mid (after put)", midHnd, 0x99);
        checkInt("t.fold_src (undisturbed by folded put)", srcHnd, 0x18 ^ 0x3c);
        topp->eval();
        checkInt("t.fold_mid (deposit discarded)", midHnd, 0x18 ^ 0x3c);
    }

    // sibalias: sibling aliases of one canonical must not share storage - a deposit into one
    // must not be visible through the other, nor disturb the canonical
    {
        vpiHandle canonHnd = mustFind("t.sib_canon");
        vpiHandle bHnd = mustFind("t.sib_b");
        vpiHandle cHnd = mustFind("t.sib_c");
        if (errors) return 10;

        topp->a = 0x11;
        topp->eval();
        const int want = (0x11 ^ 0x5a) & 0xff;
        checkInt("t.sib_b (tracks canonical)", bHnd, want);
        checkInt("t.sib_c (tracks canonical)", cHnd, want);

        putInt(bHnd, 0x03);
        putInt(cHnd, 0x02);
        checkInt("t.sib_b (after both puts)", bHnd, 0x03);
        checkInt("t.sib_c (after both puts)", cHnd, 0x02);
        checkInt("t.sib_canon (undisturbed)", canonHnd, want);
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
