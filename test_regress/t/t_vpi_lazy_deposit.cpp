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
// IEEE 1800-2023 38.34 on --vpi-lazy reconstructed rows: a deposit overrides the value the
// cone resolves to, what resolves from it re-resolves, and no rebuild takes the override back.
// Driven through a dependent cone, through the rows either side of a deposited one, and once
// per vpi_put_value store path -- two of those (vpiBinStrVal, vpiRealVal) used to reach
// storage without claiming the row, and vpi_put_value_array used to claim after a rejected
// put. Values are derived from the RTL, so a wrong answer names the signal that gave it.
//*************************************************************************

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE
#include "vpi_user.h"

#include <cmath>
#include <cstdio>
#include <cstring>
#include <functional>
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

double readReal(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiRealVal;
    vpi_get_value(handle, &value);
    return value.value.real;
}

void checkInt(const char* name, vpiHandle handle, int expected) {
    const int got = readInt(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, got);
        ++errors;
    }
}

void checkReal(const char* name, vpiHandle handle, double expected) {
    const double got = readReal(handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %g, got %g\n", name, expected, got);
        ++errors;
    }
}

void putInt(const char* name, vpiHandle handle, int value, PLI_INT32 flags = vpiNoDelay) {
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = value;
    if (!vpi_put_value(handle, &wr, nullptr, flags)) {
        std::printf("%%Error: failed to write %s\n", name);
        ++errors;
    }
}

void putBinStr(const char* name, vpiHandle handle, const char* bits) {
    s_vpi_value wr{};
    wr.format = vpiBinStrVal;
    char buf[64];
    std::strncpy(buf, bits, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = '\0';
    wr.value.str = buf;
    if (!vpi_put_value(handle, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write %s as vpiBinStrVal\n", name);
        ++errors;
    }
}

void putReal(const char* name, vpiHandle handle, double value) {
    s_vpi_value wr{};
    wr.format = vpiRealVal;
    wr.value.real = value;
    if (!vpi_put_value(handle, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write %s as vpiRealVal\n", name);
        ++errors;
    }
}

// Rejections are reported through vpi_chk_error, which the next VPI call resets, so each use
// pairs with exactly one preceding put. The caller must have cleared fatalOnVpiError, or the
// diagnostic aborts the process before it can be inspected.
void expectRejected(const char* what) {
    s_vpi_error_info info{};
    if (!vpi_chk_error(&info)) {
        std::printf("%%Error: %s was not diagnosed\n", what);
        ++errors;
    }
}

void expectAccepted(const char* what) {
    s_vpi_error_info info{};
    if (vpi_chk_error(&info)) {
        std::printf("%%Error: %s was diagnosed: %s\n", what, info.message);
        ++errors;
    }
}

// t.keep is the only storage, so every epoch bump below is a deposit into it
constexpr int KEEP_BASE = 0x24;
constexpr int KEEP_BUMP1 = 0x42;
constexpr int KEEP_BUMP2 = 0x53;

constexpr int srcOf(int keep) { return (keep ^ 0x11) & 0xff; }
constexpr int midFrom(int src) { return (src + 0x3) & 0xff; }
constexpr int topFrom(int mid) { return (mid ^ 0x2c) & 0xff; }
constexpr int aOf(int keep) { return (keep + 0x6) & 0xff; }
constexpr int bFrom(int a) { return (a ^ 0x1) & 0xff; }
constexpr int cFrom(int b) { return (b + 0x1f) & 0xff; }
constexpr int binOf(int keep) { return (keep ^ 0x5a) & 0xff; }
constexpr int binDepFrom(int bin) { return (bin + 0x7) & 0xff; }
constexpr double rOf(int keep) { return keep * 2.0; }
constexpr double rDepFrom(double r) { return r + 1.0; }
constexpr int arrOf(int keep, int idx) { return (keep ^ (0x11 * idx)) & 0xff; }

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
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;
    cycle();

    vpiHandle keeph = mustFind("t.keep");
    vpiHandle depSrch = mustFind("t.dep_src");
    vpiHandle depMidh = mustFind("t.dep_mid");
    vpiHandle depToph = mustFind("t.dep_top");
    vpiHandle pairAh = mustFind("t.pair_a");
    vpiHandle pairBh = mustFind("t.pair_b");
    vpiHandle pairCh = mustFind("t.pair_c");
    vpiHandle binRowh = mustFind("t.bin_row");
    vpiHandle binDeph = mustFind("t.bin_dep");
    vpiHandle rRowh = mustFind("t.r_row");
    vpiHandle rDeph = mustFind("t.r_dep");
    vpiHandle arrh = mustFind("t.arr");
    if (errors) return 10;

    vpiHandle arr0h = vpi_handle_by_index(arrh, 0);
    vpiHandle arr2h = vpi_handle_by_index(arrh, 2);
    if (!arr0h || !arr2h) {
        std::printf("%%Error: failed to index t.arr\n");
        return 10;
    }

    // A deposit into the flop lands in real storage; the eval retires it as a deposit but
    // leaves the value, so every sequence below starts from the same model state
    const auto reset = [&]() {
        putInt("t.keep", keeph, KEEP_BASE);
        topp->eval();
        checkInt("t.keep (settled)", keeph, KEEP_BASE);
    };

    // Deposit into a cone row, then get that row's cone rebuilt under the deposit by reading a
    // cone that resolves from it. Reading is what rebuilds, so reading the dependents before
    // the deposit as well ('preRead') is a different execution: it must give the same answers,
    // or the override depends on when the client looked. The checkInt calls inside are what
    // carry that; the returned word only feeds the compare below.
    const auto depositSequence = [&](bool preRead) {
        reset();
        if (preRead) {
            checkInt("t.dep_mid (before deposit)", depMidh, midFrom(srcOf(KEEP_BASE)));
            checkInt("t.dep_top (before deposit)", depToph, topFrom(midFrom(srcOf(KEEP_BASE))));
        }
        putInt("t.dep_src", depSrch, 0x09);
        checkInt("t.dep_src (deposit)", depSrch, 0x09);

        // A deposit into retained storage bumps the epoch, so every cone memo misses
        putInt("t.keep", keeph, KEEP_BUMP1);
        checkInt("t.dep_mid (resolves from the deposit)", depMidh, midFrom(0x09));

        putInt("t.keep", keeph, KEEP_BUMP2);
        // The rebuild the read above ran must not have committed over the deposited row
        checkInt("t.dep_src (survives a dependent's rebuild)", depSrch, 0x09);
        checkInt("t.dep_mid (agrees with t.dep_src)", depMidh, midFrom(0x09));
        checkInt("t.dep_top (transitive through two cones)", depToph, topFrom(midFrom(0x09)));

        // Cones that do not read the deposited row still track the model
        checkInt("t.pair_a (unaffected by the deposit)", pairAh, aOf(KEEP_BUMP2));

        const int observed = (readInt(depSrch) << 16) | (readInt(depMidh) << 8) | readInt(depToph);

        topp->eval();
        checkInt("t.dep_src (retired at eval)", depSrch, srcOf(KEEP_BUMP2));
        checkInt("t.dep_mid (retired at eval)", depMidh, midFrom(srcOf(KEEP_BUMP2)));
        checkInt("t.dep_top (retired at eval)", depToph, topFrom(midFrom(srcOf(KEEP_BUMP2))));
        return observed;
    };

    const int depositLate = depositSequence(false);
    const int depositEarly = depositSequence(true);
    // CONSISTENCY GUARD WITH NO DISCRIMINATING POWER OF ITS OWN, not a proof of order
    // independence. Every value this word packs is pinned to the model by a checkInt in both
    // orders above, and nothing bumps the epoch between those reads and these, so the compare
    // can only fire after one of them already has - and no probe has made it fire alone. Order
    // independence is covered by running depositSequence() both ways, not by this line.
    if (depositLate != depositEarly) {
        std::printf("%%Error: reading the dependents first changed the result: 0x%06x vs 0x%06x\n",
                    depositLate, depositEarly);
        ++errors;
    }

    // MULTI-ROW CONE. pair_a, pair_b and pair_c are three rows of one cone; depositing the
    // middle one leaves a row above it that must keep following the model and a row below it
    // that must follow the deposit. A guard that skipped the whole cone body would hold both
    // at their pre-deposit values, and one that skipped nothing would lose the deposit.
    const auto multiRowSequence = [&](bool readUpstreamFirst) {
        reset();
        checkInt("t.pair_a (before deposit)", pairAh, aOf(KEEP_BASE));
        checkInt("t.pair_c (before deposit)", pairCh, cFrom(bFrom(aOf(KEEP_BASE))));
        putInt("t.pair_b", pairBh, 0x5a);
        putInt("t.keep", keeph, KEEP_BUMP1);
        if (readUpstreamFirst) {
            checkInt("t.pair_a (row above the deposit recomputes)", pairAh, aOf(KEEP_BUMP1));
            checkInt("t.pair_c (row below resolves from the deposit)", pairCh, cFrom(0x5a));
        } else {
            checkInt("t.pair_c (row below resolves from the deposit)", pairCh, cFrom(0x5a));
            checkInt("t.pair_a (row above the deposit recomputes)", pairAh, aOf(KEEP_BUMP1));
        }
        checkInt("t.pair_b (survives its own cone's rebuild)", pairBh, 0x5a);
        topp->eval();
        checkInt("t.pair_a (retired at eval)", pairAh, aOf(KEEP_BUMP1));
        checkInt("t.pair_b (retired at eval)", pairBh, bFrom(aOf(KEEP_BUMP1)));
        checkInt("t.pair_c (retired at eval)", pairCh, cFrom(bFrom(aOf(KEEP_BUMP1))));
    };
    multiRowSequence(true);
    multiRowSequence(false);

    // Two rows of one cone deposited: the rebuild between them keeps both, and the row between
    // resolves from the upstream deposit rather than from the model
    reset();
    putInt("t.pair_a", pairAh, 0x31);
    putInt("t.pair_c", pairCh, 0x62);
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.pair_a (deposit)", pairAh, 0x31);
    checkInt("t.pair_b (resolves from the deposited row above)", pairBh, bFrom(0x31));
    checkInt("t.pair_c (deposit, not the value its cone would commit)", pairCh, 0x62);
    topp->eval();
    checkInt("t.pair_a (retired at eval)", pairAh, aOf(KEEP_BUMP1));
    checkInt("t.pair_c (retired at eval)", pairCh, cFrom(bFrom(aOf(KEEP_BUMP1))));

    // vpiInertialDelay defers the put and replays it through the same path at the flush
    reset();
    {
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x77;
        s_vpi_time when{};
        when.type = vpiSimTime;
        if (!vpi_put_value(depSrch, &wr, &when, vpiInertialDelay)) {
            std::printf("%%Error: failed to queue an inertial-delay write to t.dep_src\n");
            ++errors;
        }
    }
    checkInt("t.dep_src (inertial put not yet applied)", depSrch, srcOf(KEEP_BASE));
    VerilatedVpi::doInertialPuts();
    checkInt("t.dep_src (inertial put applied)", depSrch, 0x77);
    checkInt("t.dep_mid (resolves from the inertial deposit)", depMidh, midFrom(0x77));
    topp->eval();
    checkInt("t.dep_src (inertial deposit retired at eval)", depSrch, srcOf(KEEP_BASE));

    // vpiPropagateOff overrides the row without re-resolving what reads it: no epoch bump, so
    // the memoised dependent cone keeps the value it last resolved to
    reset();
    checkInt("t.dep_mid (memoised before the put)", depMidh, midFrom(srcOf(KEEP_BASE)));
    putInt("t.dep_src", depSrch, 0x33, vpiNoDelay | vpiPropagateOff);
    checkInt("t.dep_src (deposit with vpiPropagateOff)", depSrch, 0x33);
    checkInt("t.dep_mid (not re-resolved)", depMidh, midFrom(srcOf(KEEP_BASE)));
    // The flag suppressed the bump, not the override, so the next rebuild still sees it
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.dep_mid (re-resolved at the next epoch)", depMidh, midFrom(0x33));
    checkInt("t.dep_src (deposit stands)", depSrch, 0x33);
    topp->eval();
    checkInt("t.dep_src (retired at eval)", depSrch, srcOf(KEEP_BUMP1));

    // ---- vpiBinStrVal ----------------------------------------------------------------
    // The arm writes the row a byte at a time rather than through the word funnel, which is
    // how it came to store without claiming.
    reset();
    checkInt("t.bin_row (before deposit)", binRowh, binOf(KEEP_BASE));
    checkInt("t.bin_dep (before deposit)", binDeph, binDepFrom(binOf(KEEP_BASE)));

    putBinStr("t.bin_row", binRowh, "10010110");  // 0x96
    expectAccepted("vpiBinStrVal deposit into t.bin_row");
    checkInt("t.bin_row (vpiBinStrVal deposit)", binRowh, 0x96);

    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.bin_dep (resolves from the vpiBinStrVal deposit)", binDeph, binDepFrom(0x96));

    putInt("t.keep", keeph, KEEP_BUMP2);
    checkInt("t.bin_row (survives a dependent's rebuild)", binRowh, 0x96);
    checkInt("t.bin_dep (agrees with t.bin_row)", binDeph, binDepFrom(0x96));

    topp->eval();
    checkInt("t.bin_row (retired at eval)", binRowh, binOf(KEEP_BUMP2));
    checkInt("t.bin_dep (retired at eval)", binDeph, binDepFrom(binOf(KEEP_BUMP2)));

    // Shorter than the row: the arm zeroes the bits the string does not cover, so a short
    // string deposits a whole-row value rather than merging, unlike vpiOctStrVal below
    reset();
    putBinStr("t.bin_row", binRowh, "1011");  // 0x0b
    checkInt("t.bin_row (short vpiBinStrVal string)", binRowh, 0x0b);
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.bin_dep (resolves from the short deposit)", binDeph, binDepFrom(0x0b));
    topp->eval();

    // ---- the remaining store paths ---------------------------------------------------
    // These already claimed before this round, so they discriminate for nothing; they pin the
    // contract's "every format deposits" on a cone row, which only vpiOctStrVal on a copy row
    // (t_vpi_lazy) had covered.
    const auto sweep = [&](const char* label, int expect, const std::function<void()>& put) {
        reset();
        put();
        checkInt(label, binRowh, expect);
        putInt("t.keep", keeph, KEEP_BUMP1);
        checkInt(label, binDeph, binDepFrom(expect));
        checkInt(label, binRowh, expect);
        topp->eval();
        checkInt(label, binRowh, binOf(KEEP_BUMP1));
    };

    sweep("t.bin_row (vpiVectorVal deposit)", 0x21, [&]() {
        s_vpi_vecval vec{};
        vec.aval = 0x21;
        s_vpi_value wr{};
        wr.format = vpiVectorVal;
        wr.value.vector = &vec;
        if (!vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) ++errors;
    });
    // Three digits, not two: the arm stores only the digits given, so "41" would merge the
    // refreshed row's top two bits back in rather than replace the row
    sweep("t.bin_row (vpiOctStrVal deposit)", 0x21, [&]() {
        char str[] = "041";
        s_vpi_value wr{};
        wr.format = vpiOctStrVal;
        wr.value.str = str;
        if (!vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) ++errors;
    });
    sweep("t.bin_row (vpiDecStrVal deposit)", 0x21, [&]() {
        char str[] = "33";
        s_vpi_value wr{};
        wr.format = vpiDecStrVal;
        wr.value.str = str;
        if (!vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) ++errors;
    });
    sweep("t.bin_row (vpiHexStrVal deposit)", 0x21, [&]() {
        char str[] = "21";
        s_vpi_value wr{};
        wr.format = vpiHexStrVal;
        wr.value.str = str;
        if (!vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) ++errors;
    });
    sweep("t.bin_row (vpiStringVal deposit, byte-packed arm)", 0x21, [&]() {
        char str[] = "!";
        s_vpi_value wr{};
        wr.format = vpiStringVal;
        wr.value.str = str;
        if (!vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) ++errors;
    });
    // One bit wide, so it merges with the refreshed row rather than replacing it
    sweep("t.bin_row (vpiScalarVal deposit)", binOf(KEEP_BASE) | 1, [&]() {
        s_vpi_value wr{};
        wr.format = vpiScalarVal;
        wr.value.scalar = vpi1;
        if (!vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) ++errors;
    });

    // ---- vpiRealVal ------------------------------------------------------------------
    reset();
    checkReal("t.r_row (before deposit)", rRowh, rOf(KEEP_BASE));
    checkReal("t.r_dep (before deposit)", rDeph, rDepFrom(rOf(KEEP_BASE)));

    putReal("t.r_row", rRowh, 12.5);
    expectAccepted("vpiRealVal deposit into t.r_row");
    checkReal("t.r_row (vpiRealVal deposit)", rRowh, 12.5);

    putInt("t.keep", keeph, KEEP_BUMP1);
    checkReal("t.r_dep (resolves from the vpiRealVal deposit)", rDeph, rDepFrom(12.5));

    putInt("t.keep", keeph, KEEP_BUMP2);
    checkReal("t.r_row (survives a dependent's rebuild)", rRowh, 12.5);
    checkReal("t.r_dep (agrees with t.r_row)", rDeph, rDepFrom(12.5));

    topp->eval();
    checkReal("t.r_row (retired at eval)", rRowh, rOf(KEEP_BUMP2));
    checkReal("t.r_dep (retired at eval)", rDeph, rDepFrom(rOf(KEEP_BUMP2)));

    // ---- vpiRealVal rejected on a non-real row ---------------------------------------
    // vl_check_format already refuses this ahead of the format chain, so these checks pass
    // against the pre-round-4 runtime too: they are a regression guard against a later handler
    // that opens its write access before deciding, not evidence for this round's change.
    reset();
    checkInt("t.bin_row (materialised before the rejected put)", binRowh, binOf(KEEP_BASE));
    contextp->fatalOnVpiError(false);
    {
        s_vpi_value wr{};
        wr.format = vpiRealVal;
        wr.value.real = 3.25;
        if (vpi_put_value(binRowh, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: vpiRealVal put to non-real t.bin_row was accepted\n");
            ++errors;
        }
    }
    expectRejected("vpiRealVal put to non-real t.bin_row");
    checkInt("t.bin_row (unchanged by the rejected put)", binRowh, binOf(KEEP_BASE));
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.bin_row (still resolves from its cone)", binRowh, binOf(KEEP_BUMP1));
    checkInt("t.bin_dep (still resolves from its cone)", binDeph, binDepFrom(binOf(KEEP_BUMP1)));
    contextp->fatalOnVpiError(true);
    topp->eval();

    // ---- vpi_put_value_array accepted ------------------------------------------------
    // Granularity is the whole variable: the array carries one deposit word, so a put of two
    // elements pins all four against the rebuild, and the untouched two keep their pre-put
    // values rather than following keep. That is documented behaviour, unchanged this round,
    // so it pins the contract rather than discriminating for the fix.
    reset();
    checkInt("t.arr[0] (before deposit)", arr0h, arrOf(KEEP_BASE, 0));
    checkInt("t.arr[2] (before deposit)", arr2h, arrOf(KEEP_BASE, 2));
    {
        PLI_UINT32 words[2] = {0x71, 0x72};
        s_vpi_arrayvalue av{};
        av.format = vpiIntVal;
        av.value.integers = reinterpret_cast<PLI_INT32*>(words);
        PLI_INT32 index = 0;
        vpi_put_value_array(arrh, &av, &index, 2);
    }
    expectAccepted("vpi_put_value_array into t.arr");
    checkInt("t.arr[0] (array deposit)", arr0h, 0x71);
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.arr[0] (array deposit survives a rebuild)", arr0h, 0x71);
    checkInt("t.arr[2] (row pinned whole, so still the pre-put value)", arr2h,
             arrOf(KEEP_BASE, 2));
    topp->eval();
    checkInt("t.arr[0] (retired at eval)", arr0h, arrOf(KEEP_BUMP1, 0));
    checkInt("t.arr[2] (retired at eval)", arr2h, arrOf(KEEP_BUMP1, 2));

    // ---- vpi_put_value_array rejected: unsupported format ----------------------------
    // vl_check_array_format now runs ahead of the write access. Claiming after a rejection
    // would pin every element of t.arr at its pre-put value until the next eval step.
    reset();
    checkInt("t.arr[0] (materialised before the rejected format put)", arr0h, arrOf(KEEP_BASE, 0));
    contextp->fatalOnVpiError(false);
    {
        double reals[2] = {1.0, 2.0};
        s_vpi_arrayvalue av{};
        av.format = vpiRealVal;
        av.value.reals = reals;
        PLI_INT32 index = 0;
        vpi_put_value_array(arrh, &av, &index, 2);
    }
    expectRejected("vpi_put_value_array with an unsupported format");
    checkInt("t.arr[0] (unchanged by the rejected put)", arr0h, arrOf(KEEP_BASE, 0));
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.arr[0] (rejected format claimed nothing)", arr0h, arrOf(KEEP_BUMP1, 0));
    checkInt("t.arr[2] (rejected format claimed nothing)", arr2h, arrOf(KEEP_BUMP1, 2));
    contextp->fatalOnVpiError(true);
    topp->eval();

    // ---- vpi_put_value_array rejected: too many elements -----------------------------
    // The bounds check moved ahead of the write access too, which is what moved its
    // diagnostic's function name from vl_put_value_array to vpi_put_value_array.
    reset();
    checkInt("t.arr[0] (materialised before the oversized put)", arr0h, arrOf(KEEP_BASE, 0));
    contextp->fatalOnVpiError(false);
    {
        PLI_UINT32 words[8] = {0, 1, 2, 3, 4, 5, 6, 7};
        s_vpi_arrayvalue av{};
        av.format = vpiIntVal;
        av.value.integers = reinterpret_cast<PLI_INT32*>(words);
        PLI_INT32 index = 0;
        vpi_put_value_array(arrh, &av, &index, 8);
    }
    expectRejected("vpi_put_value_array with num beyond the array size");
    checkInt("t.arr[0] (unchanged by the oversized put)", arr0h, arrOf(KEEP_BASE, 0));
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.arr[0] (oversized put claimed nothing)", arr0h, arrOf(KEEP_BUMP1, 0));
    checkInt("t.arr[2] (oversized put claimed nothing)", arr2h, arrOf(KEEP_BUMP1, 2));
    contextp->fatalOnVpiError(true);
    topp->eval();

    // ---- vpi_put_value_array of no elements ------------------------------------------
    // Storing nothing is not a write: it raises no error, but claiming the row would pin
    // every element at its pre-put value until the next eval step.
    reset();
    checkInt("t.arr[0] (materialised before the empty put)", arr0h, arrOf(KEEP_BASE, 0));
    {
        PLI_UINT32 words[1] = {0x99};
        s_vpi_arrayvalue av{};
        av.format = vpiIntVal;
        av.value.integers = reinterpret_cast<PLI_INT32*>(words);
        PLI_INT32 index = 0;
        vpi_put_value_array(arrh, &av, &index, 0);
    }
    expectAccepted("vpi_put_value_array of zero elements");
    checkInt("t.arr[0] (unchanged by the empty put)", arr0h, arrOf(KEEP_BASE, 0));
    putInt("t.keep", keeph, KEEP_BUMP1);
    checkInt("t.arr[0] (empty put claimed nothing)", arr0h, arrOf(KEEP_BUMP1, 0));
    checkInt("t.arr[2] (empty put claimed nothing)", arr2h, arrOf(KEEP_BUMP1, 2));
    topp->eval();

    // A clock edge recomputes everything from the flop, deposits long gone
    reset();
    putInt("t.dep_src", depSrch, 0x09);
    putInt("t.pair_b", pairBh, 0x5a);
    putBinStr("t.bin_row", binRowh, "10010110");
    putReal("t.r_row", rRowh, 12.5);
    cycle();
    const int keepAfter = (KEEP_BASE + 0x3) & 0xff;
    checkInt("t.keep (clocked)", keeph, keepAfter);
    checkInt("t.dep_src (clocked)", depSrch, srcOf(keepAfter));
    checkInt("t.dep_mid (clocked)", depMidh, midFrom(srcOf(keepAfter)));
    checkInt("t.dep_top (clocked)", depToph, topFrom(midFrom(srcOf(keepAfter))));
    checkInt("t.pair_a (clocked)", pairAh, aOf(keepAfter));
    checkInt("t.pair_b (clocked)", pairBh, bFrom(aOf(keepAfter)));
    checkInt("t.pair_c (clocked)", pairCh, cFrom(bFrom(aOf(keepAfter))));
    checkInt("t.bin_row (clocked)", binRowh, binOf(keepAfter));
    checkInt("t.bin_dep (clocked)", binDeph, binDepFrom(binOf(keepAfter)));
    checkReal("t.r_row (clocked)", rRowh, rOf(keepAfter));
    checkReal("t.r_dep (clocked)", rDeph, rDepFrom(rOf(keepAfter)));
    checkInt("t.arr[0] (clocked)", arr0h, arrOf(keepAfter, 0));

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
