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
// Values computed directly; exact expectations derived from RTL.
//*************************************************************************

#include "verilated.h"
#include "verilated_vpi.h"

#include "Vt_vpi_lazy_public_rw_accuracy.h"
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

unsigned readVecLow32(vpiHandle handle) {  // Read low 32 bits
    s_vpi_value value{};
    value.format = vpiVectorVal;
    vpi_get_value(handle, &value);
    return static_cast<unsigned>(value.value.vector[0].aval);
}

void checkInt(const char* name, vpiHandle handle, int expected) {
    const int got = readInt(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, got);
        ++errors;
    }
}

void checkVec(const char* name, vpiHandle handle, unsigned expected) {
    const unsigned got = readVecLow32(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0u, got %0u\n", name, expected, got);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_accuracy> topp{
        new Vt_vpi_lazy_public_rw_accuracy{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
    };

    topp->rst = 1;  // Reset
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    // Software model: vpi_get_value returns raw bit patterns (not sign-extended)
    int keep = 0;
    int skeep = 0;
    unsigned wkeep = 0;
    // Registered state (one cycle delay)
    int result = 0;
    int woPlain = 0;
    int woSigned = 0;
    unsigned woWide = 0;
    int cfLatch = 0;
    const auto cmb1Of = [](int k) { return (k + 0x7) & 0x7f; };
    const auto cmb2Of = [&](int k) { return (cmb1Of(k) ^ 0x2a) & 0x7f; };
    const auto cmb3Of = [&](int k) { return (cmb2Of(k) + 0x5) & 0x7f; };
    const auto scmbOf = [](int sk) { return (sk - 3) & 0x7f; };
    const auto wcmbOf = [](unsigned wk) { return wk + 1; };
    const auto subOutOf = [](int k) { return (k ^ 0x15) & 0x7f; };
    const auto bselOf = [](int k) { return (k >> 2) & 0x1; };
    const auto mux0Of = [&](int k) { return (k & 0x1) ? cmb1Of(k) : cmb2Of(k); };
    const auto pselOf
        = [&](int k) { return (((mux0Of(k) & 0xf) << 3) | ((k >> 4) & 0x7)) & 0x7f; };
    const auto sshiftOf = [](int sk) {
        const int se = (sk & 0x40) ? (sk | ~0x7f) : sk;
        return (se >> 2) & 0x7f;
    };
    const auto wselOf = [](unsigned wk) { return (wk << 3) & 0xffffffffu; };
    const auto cfUncondOf = [](int k) { return (k ^ 0x11) & 0x7f; };
    const auto cfIfElseOf = [](int k) { return (k & 0x1) ? ((k + 1) & 0x7f) : ((k - 1) & 0x7f); };
    const auto cfIfDefOf = [](int k) { return (k & 0x2) ? ((~k) & 0x7f) : ((k + 4) & 0x7f); };
    const auto cfReadsReconOf = [&](int k) { return (cmb1Of(k) ^ 0x2) & 0x7f; };
    const auto cfReadsCombOf = [&](int k) { return (cfUncondOf(k) + 0x3) & 0x7f; };
    const auto cfPartialOf = [](int k) { return k & 0xf; };
    const auto cfCaseOf = [](int k) {
        switch (k & 0x3) {
        case 0: return k & 0x7f;
        case 1: return (k + 1) & 0x7f;
        case 2: return (k + 2) & 0x7f;
        default: return (k + 3) & 0x7f;
        }
    };
    const auto cfVlsbOf = [](int k, int sk) {
        const int base = (k << 1) & 0xff;
        const int lsb = (k & 0x3) * 2;
        return ((base & ~(0x3 << lsb)) | ((sk & 0x3) << lsb)) & 0xff;
    };
    const auto cfCasePartOf = [](int k, int sk) {
        switch (k & 0x3) {
        case 0: return (k + 1) & 0x7f;
        case 1: return ((k & 0x70) | (sk & 0xf)) & 0x7f;
        default: return (~k) & 0x7f;
        }
    };
    const auto cfMtaOf = [](int k) { return (k + 0x6) & 0x7f; };
    const auto cfMtbOf = [](int k) { return ((k + 0x6) ^ 0x1) & 0x7f; };
    const auto cfPortopOf = [](int k) { return k & 0x7f; };
    const auto cfCtvOf = [](int k, int sk) { return (((sk & 0xf) << 4) | (k & 0xf)) & 0xff; };
    const auto cfCtsOf = [](int k, int sk) { return (((k & 0xf) << 4) | (sk & 0xf)) & 0xff; };

    vpiHandle cmb1 = mustFind("t.cmb1");
    vpiHandle cmb2 = mustFind("t.cmb2");
    vpiHandle cmb3 = mustFind("t.cmb3");
    vpiHandle keeph = mustFind("t.keep");
    vpiHandle scmb = mustFind("t.scmb");
    vpiHandle skeeph = mustFind("t.skeep");
    vpiHandle wcmb = mustFind("t.wcmb");
    vpiHandle alias1 = mustFind("t.alias1");
    vpiHandle alias2 = mustFind("t.alias2");
    vpiHandle subOut = mustFind("t.sub_out");
    vpiHandle observe = mustFind("observe");
    vpiHandle bsel = mustFind("t.bsel");
    vpiHandle mux0 = mustFind("t.mux0");
    vpiHandle psel = mustFind("t.psel");
    vpiHandle sshift = mustFind("t.sshift");
    vpiHandle wsel = mustFind("t.wsel");
    vpiHandle pcomb = mustFind("t.pcomb");
    vpiHandle cfUncond = mustFind("t.cf_uncond");
    vpiHandle cfIfElse = mustFind("t.cf_ifelse");
    vpiHandle cfIfDef = mustFind("t.cf_ifdef");
    vpiHandle cfReadsRecon = mustFind("t.cf_readsrecon");
    vpiHandle cfReadsComb = mustFind("t.cf_readscomb");
    vpiHandle cfLatchH = mustFind("t.cf_latch");
    vpiHandle cfPartialH = mustFind("t.cf_partial");
    vpiHandle cfCaseH = mustFind("t.cf_case");
    vpiHandle cfVlsbH = mustFind("t.cf_vlsb");
    vpiHandle cfCasePartH = mustFind("t.cf_casepart");
    vpiHandle cfMtaH = mustFind("t.cf_mta");
    vpiHandle cfMtbH = mustFind("t.cf_mtb");
    vpiHandle cfNopreH = mustFind("t.cf_nopre");
    vpiHandle cfSelfReadH = mustFind("t.cf_selfread");
    vpiHandle cfCtvH = mustFind("t.cf_ctv");
    vpiHandle cfCtsH = mustFind("t.cf_cts");
    vpiHandle cfMixFullH = mustFind("t.cf_mixfull");
    vpiHandle cfOvlH = mustFind("t.cf_ovl");
    vpiHandle rstH = mustFind("t.rst");
    vpiHandle cfPortopH = mustFind("t.cf_portop");
    vpiHandle woPlainH = mustFind("t.wo_plain");
    vpiHandle woSignedH = mustFind("t.wo_signed");
    vpiHandle woWideH = mustFind("t.wo_wide");
    if (errors) return 10;

    for (int i = 0; i < 5; ++i) {
        const int prevKeep = keep;
        const int prevSkeep = skeep;
        const unsigned prevWkeep = wkeep;
        cycle();
        result = cmb3Of(prevKeep);
        woPlain = (prevKeep + 0x9) & 0x7f;
        woSigned = (prevSkeep - 1) & 0x7f;
        woWide = prevWkeep + 11;
        keep = (keep + 0x3) & 0x7f;
        skeep = (skeep - 2) & 0x7f;
        wkeep = wkeep + 5;
        if ((keep >> 2) & 0x1) cfLatch = keep;  // Genuine latch

        checkInt("t.keep", keeph, keep);
        checkInt("t.cmb1", cmb1, cmb1Of(keep));
        checkInt("t.cmb2", cmb2, cmb2Of(keep));
        checkInt("t.cmb3", cmb3, cmb3Of(keep));
        checkInt("t.skeep", skeeph, skeep);
        checkInt("t.scmb", scmb, scmbOf(skeep));
        checkVec("t.wcmb", wcmb, wcmbOf(wkeep));
        checkInt("t.alias1", alias1, keep);
        checkInt("t.alias2", alias2, keep);
        checkInt("t.sub_out", subOut, subOutOf(keep));
        checkInt("t.bsel", bsel, bselOf(keep));
        checkInt("t.mux0", mux0, mux0Of(keep));
        checkInt("t.psel", psel, pselOf(keep));
        checkInt("t.sshift", sshift, sshiftOf(skeep));
        checkVec("t.wsel", wsel, wselOf(wkeep));
        checkInt("t.pcomb", pcomb, (keep ^ result) & 0x7f);
        checkInt("t.cf_uncond", cfUncond, cfUncondOf(keep));
        checkInt("t.cf_ifelse", cfIfElse, cfIfElseOf(keep));
        checkInt("t.cf_ifdef", cfIfDef, cfIfDefOf(keep));
        checkInt("t.cf_readsrecon", cfReadsRecon, cfReadsReconOf(keep));
        checkInt("t.cf_readscomb", cfReadsComb, cfReadsCombOf(keep));
        checkInt("t.cf_latch", cfLatchH, cfLatch);
        checkInt("t.cf_partial", cfPartialH, cfPartialOf(keep));
        checkInt("t.cf_vlsb", cfVlsbH, cfVlsbOf(keep, skeep));
        checkInt("t.cf_case", cfCaseH, cfCaseOf(keep));
        checkInt("t.cf_casepart", cfCasePartH, cfCasePartOf(keep, skeep));
        checkInt("t.cf_mta", cfMtaH, cfMtaOf(keep));
        checkInt("t.cf_mtb", cfMtbH, cfMtbOf(keep));
        checkInt("t.cf_selfread", cfSelfReadH, (keep + 1) & 0x7f);
        checkInt("t.cf_ctv", cfCtvH, cfCtvOf(keep, skeep));
        checkInt("t.cf_cts", cfCtsH, cfCtsOf(keep, skeep));
        checkInt("t.rst", rstH, 0);
        checkInt("t.cf_portop", cfPortopH, cfPortopOf(keep));
        checkInt("t.wo_plain", woPlainH, woPlain);
        checkInt("t.wo_signed", woSignedH, woSigned);
        checkVec("t.wo_wide", woWideH, woWide);
    }
    (void)observe;

    // Callbacks
    int cmb1CbCount = 0;
    int cmb1CbLast = -1;
    static int* const cmb1CbCountP = &cmb1CbCount;
    static int* const cmb1CbLastP = &cmb1CbLast;
    const auto cmb1Cb = [](p_cb_data cb_data) -> PLI_INT32 {
        ++(*cmb1CbCountP);
        *cmb1CbLastP = cb_data->value->value.integer;
        return 0;
    };
    s_vpi_value cbValue{};
    cbValue.format = vpiIntVal;
    s_cb_data cbData{};
    cbData.reason = cbValueChange;
    cbData.cb_rtn = cmb1Cb;
    cbData.obj = cmb1;
    cbData.value = &cbValue;
    vpiHandle cbH = vpi_register_cb(&cbData);
    if (!cbH) {
        std::printf("%%Error: failed to register cbValueChange on t.cmb1\n");
        return 11;
    }
    cycle();
    keep = (keep + 0x3) & 0x7f;
    skeep = (skeep - 2) & 0x7f;
    VerilatedVpi::callValueCbs();
    if (cmb1CbCount <= 0) {
        std::printf("%%Error: cbValueChange on reconstructed t.cmb1 did not fire\n");
        ++errors;
    }
    if (cmb1CbLast != cmb1Of(keep)) {
        std::printf("%%Error: cbValueChange delivered %0d, expected %0d\n", cmb1CbLast,
                    cmb1Of(keep));
        ++errors;
    }

    // Read-only signals
    Verilated::fatalOnVpiError(false);
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x11;
    vpiHandle putRet = vpi_put_value(cmb2, &wr, nullptr, vpiNoDelay);
    if (putRet) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cmb2 unexpectedly succeeded\n");
        ++errors;
    }
    if (!vpi_chk_error(nullptr)) {
        std::printf("%%Error: expected a VPI error from writing reconstructed t.cmb2\n");
        ++errors;
    }
    checkInt("t.cmb2 (after failed write)", cmb2, cmb2Of(keep));

    wr.value.integer = -5;
    vpiHandle sPutRet = vpi_put_value(scmb, &wr, nullptr, vpiNoDelay);
    if (sPutRet) {
        std::printf("%%Error: vpi_put_value on reconstructed t.scmb unexpectedly succeeded\n");
        ++errors;
    }
    checkInt("t.scmb (after failed write)", scmb, scmbOf(skeep));

    wr.value.integer = 0x7;
    if (vpi_put_value(psel, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.psel unexpectedly succeeded\n");
        ++errors;
    }
    checkInt("t.psel (after failed write)", psel, pselOf(keep));

    wr.value.integer = 0x9;
    if (vpi_put_value(cfUncond, &wr, nullptr, vpiNoDelay)) {
        std::printf(
            "%%Error: vpi_put_value on reconstructed t.cf_uncond unexpectedly succeeded\n");
        ++errors;
    }
    checkInt("t.cf_uncond (after failed write)", cfUncond, cfUncondOf(keep));

    bool foldRetained = false;
    for (int i = 1; i < argc; ++i) {
        if (0 == std::strcmp(argv[i], "+lazy-fold-retained")) foldRetained = true;
    }
    wr.value.integer = 0x5;
    if (foldRetained) {
        if (!vpi_put_value(cfPartialH, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write retained t.cf_partial\n");
            ++errors;
        }
        checkInt("t.cf_partial (after put)", cfPartialH, 0x5);
        cycle();
        keep = (keep + 0x3) & 0x7f;
        skeep = (skeep - 2) & 0x7f;
    } else if (vpi_put_value(cfPartialH, &wr, nullptr, vpiNoDelay)) {
        std::printf(
            "%%Error: vpi_put_value on reconstructed t.cf_partial unexpectedly succeeded\n");
        ++errors;
    }
    checkInt("t.cf_partial (after write)", cfPartialH, cfPartialOf(keep));

    if (!foldRetained) {
        wr.value.integer = 0x77;
        if (vpi_put_value(cfCtvH, &wr, nullptr, vpiNoDelay)) {
            std::printf(
                "%%Error: vpi_put_value on reconstructed t.cf_ctv unexpectedly succeeded\n");
            ++errors;
        }
        checkInt("t.cf_ctv (after failed write)", cfCtvH, cfCtvOf(keep, skeep));
        if (vpi_put_value(cfCtsH, &wr, nullptr, vpiNoDelay)) {
            std::printf(
                "%%Error: vpi_put_value on reconstructed t.cf_cts unexpectedly succeeded\n");
            ++errors;
        }
        checkInt("t.cf_cts (after failed write)", cfCtsH, cfCtsOf(keep, skeep));
    }
    Verilated::fatalOnVpiError(true);

    wr.value.integer = 0x2c;
    if (!vpi_put_value(cfNopreH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.cf_nopre\n");
        ++errors;
    }
    checkInt("t.cf_nopre (after put)", cfNopreH, 0x2c);

    wr.value.integer = 0x19;
    if (!vpi_put_value(cfSelfReadH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.cf_selfread\n");
        ++errors;
    }
    checkInt("t.cf_selfread (after put)", cfSelfReadH, 0x19);

    wr.value.integer = 0x2d;
    if (!vpi_put_value(cfMixFullH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.cf_mixfull\n");
        ++errors;
    }
    checkInt("t.cf_mixfull (after put)", cfMixFullH, 0x2d);
    wr.value.integer = 0x36;
    if (!vpi_put_value(cfOvlH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.cf_ovl\n");
        ++errors;
    }
    checkInt("t.cf_ovl (after put)", cfOvlH, 0x36);

    wr.value.integer = 0x2a;
    if (!vpi_put_value(woSignedH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained write-only reg t.wo_signed\n");
        ++errors;
    }
    checkInt("t.wo_signed (after put)", woSignedH, 0x2a);
    {
        const int prevSkeep = skeep;
        cycle();
        keep = (keep + 0x3) & 0x7f;
        skeep = (skeep - 2) & 0x7f;
        woSigned = (prevSkeep - 1) & 0x7f;
        checkInt("t.wo_signed (after clocked overwrite)", woSignedH, woSigned);
    }

    wr.value.integer = 0x20;
    if (!vpi_put_value(keeph, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write boundary signal t.keep\n");
        ++errors;
    }
    checkInt("t.keep (after put)", keeph, 0x20);
    keep = 0x20;
    checkInt("t.cmb1 (after put)", cmb1, cmb1Of(keep));
    checkInt("t.alias1 (after put)", alias1, keep);
    checkInt("t.cf_uncond (after put)", cfUncond, cfUncondOf(keep));
    checkInt("t.cf_readsrecon (after put)", cfReadsRecon, cfReadsReconOf(keep));

    wr.value.integer = 0x33;
    if (!vpi_put_value(alias2, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through alias t.alias2\n");
        ++errors;
    }
    keep = 0x33;
    checkInt("t.keep (via alias2 put)", keeph, keep);
    checkInt("t.alias1 (via alias2 put)", alias1, keep);
    checkInt("t.sub_out (via alias2 put)", subOut, subOutOf(keep));

    wr.value.integer = 0x15;
    if (!vpi_put_value(alias1, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through alias t.alias1\n");
        ++errors;
    }
    keep = 0x15;
    checkInt("t.keep (via alias1 put)", keeph, keep);
    checkInt("t.alias2 (via alias1 put)", alias2, keep);

    cycle();
    keep = (keep + 0x3) & 0x7f;
    checkInt("t.keep (after eval)", keeph, keep);
    checkInt("t.alias1 (after eval)", alias1, keep);
    checkInt("t.cmb3 (after eval)", cmb3, cmb3Of(keep));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
