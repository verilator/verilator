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

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};

    {
        vpiHandle paramh = mustFind("t.INTF_QTY");
        if (paramh) {
            checkInt("t.INTF_QTY", paramh, 3);
            const PLI_INT32 vtype = vpi_get(vpiType, paramh);
            if (vtype != vpiParameter) {
                std::printf("%%Error: t.INTF_QTY vpiType expected vpiParameter (%0d), got %0d\n",
                            vpiParameter, vtype);
                ++errors;
            }
        }
    }

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    topp->rst = 1;
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
    vpiHandle floorOnlyH = mustFind("t.floor_only");
    vpiHandle deadh = mustFind("t.dead");
    vpiHandle passOut = mustFind("t.pass_out");
    vpiHandle subpassPortIn = mustFind("t.u_subpass.port_in");
    vpiHandle subpassPortOut = mustFind("t.u_subpass.port_out");
    vpiHandle pinnedH = mustFind("t.pinned_rw");
    vpiHandle lazyRoH = mustFind("t.lazy_ro");
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
        checkInt("t.pass_out", passOut, keep);
        checkInt("t.u_subpass.port_in", subpassPortIn, keep);
        checkInt("t.u_subpass.port_out", subpassPortOut, keep);
        checkInt("t.pinned_rw", pinnedH, (keep ^ 0x5) & 0x7f);
        checkInt("t.lazy_ro", lazyRoH, (keep + 1) & 0x7f);
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
        checkInt("t.floor_only", floorOnlyH, result);
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

    // Reconstructed signals take deposits, dropped by the next eval.
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = 0x11;
    if (!vpi_put_value(cmb2, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cmb2 failed\n");
        ++errors;
    }
    checkInt("t.cmb2 (deposit)", cmb2, 0x11);

    wr.value.integer = -5;
    if (!vpi_put_value(scmb, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.scmb failed\n");
        ++errors;
    }
    checkInt("t.scmb (deposit)", scmb, -5 & 0x7f);

    wr.value.integer = 0x7;
    if (!vpi_put_value(psel, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.psel failed\n");
        ++errors;
    }
    checkInt("t.psel (deposit)", psel, 0x7);

    wr.value.integer = 0x9;
    if (!vpi_put_value(cfUncond, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cf_uncond failed\n");
        ++errors;
    }
    checkInt("t.cf_uncond (deposit)", cfUncond, 0x9);
    // t.cf_readscomb is reconstructed from t.cf_uncond, so it recomputes off the deposit.
    checkInt("t.cf_readscomb (from cf_uncond deposit)", cfReadsComb, (0x9 + 0x3) & 0x7f);

    // A block that writes its target in full is reconstructable, so a deposit reads back
    wr.value.integer = 0x19;
    if (!vpi_put_value(cfSelfReadH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cf_selfread failed\n");
        ++errors;
    }
    checkInt("t.cf_selfread (deposit)", cfSelfReadH, 0x19);

    wr.value.integer = 0x5;
    if (!vpi_put_value(cfPartialH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on t.cf_partial failed\n");
        ++errors;
    }
    checkInt("t.cf_partial (after put)", cfPartialH, 0x5);

    wr.value.integer = 0x77;
    if (!vpi_put_value(cfCtvH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cf_ctv failed\n");
        ++errors;
    }
    checkInt("t.cf_ctv (deposit)", cfCtvH, 0x77);
    if (!vpi_put_value(cfCtsH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on reconstructed t.cf_cts failed\n");
        ++errors;
    }
    checkInt("t.cf_cts (deposit)", cfCtsH, 0x77);

    wr.value.integer = 0x2c;
    if (!vpi_put_value(cfNopreH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write retained t.cf_nopre\n");
        ++errors;
    }
    checkInt("t.cf_nopre (after put)", cfNopreH, 0x2c);

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

    // Deposit on a write-only reg survives until the next clocked overwrite
    if (deadh) {
        wr.value.integer = 0x2a;
        if (!vpi_put_value(deadh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write retained write-only reg t.dead\n");
            ++errors;
        }
        checkInt("t.dead (after put)", deadh, 0x2a);
        const int prevKeep = keep;
        cycle();
        keep = (keep + 0x3) & 0x7f;
        skeep = (skeep - 2) & 0x7f;
        checkInt("t.dead (clocked overwrite)", deadh, (prevKeep + 0x9) & 0x7f);
    }

    // t.alias1/t.alias2/t.pass_out and the inlined subpass ports are aliases of t.keep, a flop
    // and so a boundary. Each is reconstructed from keep with its own shadow rather than
    // retargeted onto keep's storage, so a deposit into one is confined to it and transient
    // instead of mutating the counter the flop counts on from.
    const int keepPre = keep;
    wr.value.integer = 0x1a;
    if (!vpi_put_value(subpassPortOut, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through inlined port t.u_subpass.port_out\n");
        ++errors;
    }
    checkInt("t.u_subpass.port_out (deposit)", subpassPortOut, 0x1a);
    checkInt("t.keep (unchanged by port_out put)", keeph, keepPre);
    checkInt("t.alias2 (unchanged by port_out put)", alias2, keepPre);

    wr.value.integer = 0x20;
    if (!vpi_put_value(keeph, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write boundary signal t.keep\n");
        ++errors;
    }
    checkInt("t.keep (after put)", keeph, 0x20);
    keep = 0x20;
    checkInt("t.cmb1 (after put)", cmb1, cmb1Of(keep));
    checkInt("t.cf_uncond (after put)", cfUncond, cfUncondOf(keep));
    checkInt("t.cf_readsrecon (after put)", cfReadsRecon, cfReadsReconOf(keep));
    // Reconstructed from keep, so it reflects the deposit at once rather than lagging it as
    // --public-flat-rw's stored copy would: the divergence any reconstructed reader has.
    checkInt("t.alias1 (tracks keep)", alias1, keep);

    wr.value.integer = 0x33;
    if (!vpi_put_value(alias2, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through alias t.alias2\n");
        ++errors;
    }
    checkInt("t.alias2 (deposit)", alias2, 0x33);
    checkInt("t.keep (unchanged by alias2 put)", keeph, keep);
    checkInt("t.alias1 (unchanged by alias2 put)", alias1, keep);
    // sub_out is reconstructed from keep, so it tracks keep, not the alias deposit
    checkInt("t.sub_out (unchanged by alias2 put)", subOut, subOutOf(keep));

    wr.value.integer = 0x15;
    if (!vpi_put_value(alias1, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through alias t.alias1\n");
        ++errors;
    }
    checkInt("t.alias1 (deposit)", alias1, 0x15);
    checkInt("t.keep (unchanged by alias1 put)", keeph, keep);
    checkInt("t.alias2 (unchanged by alias1 put)", alias2, 0x33);

    // Pinned public_flat_rw signal keeps real storage: write sticks.
    wr.value.integer = 0x69;
    if (!vpi_put_value(pinnedH, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value on public_flat_rw t.pinned_rw failed\n");
        ++errors;
    }
    checkInt("t.pinned_rw (after put)", pinnedH, 0x69);
    checkInt("t.lazy_ro (unaffected)", lazyRoH, (keep + 1) & 0x7f);

    // The eval bumps the epoch, discarding every reconstructed shadow, and VLVF_LAZY_RETAINED
    // arms the settle re-run for the retained ones: no clock edge needed to clear the deposits.
    topp->eval();
    checkInt("t.keep (unchanged by settle)", keeph, keep);
    checkInt("t.alias1 (settle re-run)", alias1, keep);
    checkInt("t.alias2 (settle re-run)", alias2, keep);
    checkInt("t.pass_out (settle re-run)", passOut, keep);
    checkInt("t.u_subpass.port_out (settle re-run)", subpassPortOut, keep);
    checkInt("t.sub_out (settle re-run)", subOut, subOutOf(keep));

    cycle();
    keep = (keep + 0x3) & 0x7f;
    checkInt("t.keep (after eval)", keeph, keep);
    checkInt("t.alias1 (after eval)", alias1, keep);
    checkInt("t.cmb3 (after eval)", cmb3, cmb3Of(keep));
    // The pinned signal is re-driven combinationally, overwriting the deposit
    checkInt("t.pinned_rw (after eval)", pinnedH, (keep ^ 0x5) & 0x7f);

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
