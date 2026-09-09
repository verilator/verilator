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

#include "Vt_vpi_lazy_memory.h"
#include "vpi_user.h"

#include <algorithm>
#include <cstdio>
#include <memory>

namespace {

constexpr int WORDS = 16;
constexpr int LVL0 = 8;

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

void putInt(vpiHandle handle, int v) {
    s_vpi_value wr{};
    wr.format = vpiIntVal;
    wr.value.integer = v;
    if (!vpi_put_value(handle, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: vpi_put_value failed\n");
        ++errors;
    }
}

// Model of the RTL reduction tree.
void expectTree(int wdata, int addr, int lvl0[LVL0], int lvl1[4], int lvl2[2], int& picked) {
    for (int i = 0; i < LVL0; ++i) lvl0[i] = (wdata ^ (0x13 * i) ^ addr) & 0xff;
    for (int i = 0; i < 4; ++i) lvl1[i] = lvl0[2 * i] | lvl0[(2 * i) + 1];
    for (int i = 0; i < 2; ++i) lvl2[i] = lvl1[2 * i] & lvl1[(2 * i) + 1];
    picked = lvl2[addr & 1];
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_memory> topp{new Vt_vpi_lazy_memory{contextp.get(), ""}};

    int model[WORDS];

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };
    const auto rtlWrite = [&](int a, int d) {
        topp->we = 1;
        topp->addr = a;
        topp->wdata = d;
        cycle();
        model[a] = d;
    };

    vpiHandle memh = mustFind("t.mem");
    if (errors) return 10;
    vpiHandle word[WORDS];
    for (int i = 0; i < WORDS; ++i) {
        word[i] = vpi_handle_by_index(memh, i);
        if (!word[i]) {
            std::printf("%%Error: vpi_handle_by_index(t.mem, %0d) returned null\n", i);
            ++errors;
        }
    }
    if (errors) return 11;

    topp->clk = 0;
    topp->we = 0;
    topp->eval();
    for (int i = 0; i < WORDS; ++i) rtlWrite(i, (i * 0x11) & 0xff);
    topp->we = 0;

    // RTL writes observable via VPI.
    const struct {
        int addr;
        int data;
    } seq[] = {{2, 0x5a}, {7, 0xff}, {9, 0xc3}, {4, 0x80}, {13, 0x01}};
    for (const auto& w : seq) {
        rtlWrite(w.addr, w.data);
        checkInt("mem word (RTL clocked write)", word[w.addr], w.data);
    }

    // VPI write persists across eval.
    putInt(word[6], 0x99);
    model[6] = 0x99;
    checkInt("mem word (immediately after VPI put)", word[6], 0x99);
    topp->we = 0;
    topp->addr = 0;
    cycle();
    checkInt("mem word (VPI value persists across eval, we=0)", word[6], 0x99);

    // RTL wins over stale VPI write.
    putInt(word[11], 0x22);
    checkInt("mem word (immediately after VPI put)", word[11], 0x22);
    rtlWrite(11, 0x77);
    checkInt("mem word (RTL clocked store wins over stale VPI write)", word[11], 0x77);

    // Whole-array reads match model.
    for (int i = 0; i < WORDS; ++i) checkInt("mem word (whole-array readback)", word[i], model[i]);

    // vpi_iterate/vpi_scan enumeration.
    {
        vpiHandle it = vpi_iterate(vpiReg, memh);
        if (!it) {
            std::printf("%%Error: vpi_iterate(vpiReg, t.mem) returned null\n");
            ++errors;
        } else {
            int scanned[WORDS];
            int cnt = 0;
            while (vpiHandle w = vpi_scan(it)) {
                if (cnt < WORDS) scanned[cnt] = readInt(w);
                ++cnt;
            }
            if (cnt != WORDS) {
                std::printf("%%Error: vpi_scan over t.mem yielded %0d words, expected %0d\n", cnt,
                            WORDS);
                ++errors;
            } else {
                int want[WORDS];
                for (int i = 0; i < WORDS; ++i) want[i] = model[i];
                std::sort(want, want + WORDS);
                std::sort(scanned, scanned + WORDS);
                for (int i = 0; i < WORDS; ++i) {
                    if (scanned[i] != want[i]) {
                        std::printf("%%Error: vpi_scan values do not match model (sorted pos %0d: "
                                    "got %0d, want %0d)\n",
                                    i, scanned[i], want[i]);
                        ++errors;
                    }
                }
            }
        }
    }

    checkInt("t.last_wdata", mustFind("t.last_wdata"), 0x77);
    checkInt("t.last_addr", mustFind("t.last_addr"), 11);

    // Reconstructed combinational unpacked arrays.
    vpiHandle lvl0h = mustFind("t.lvl0");
    vpiHandle lvl1h = mustFind("t.lvl1");
    vpiHandle lvl2h = mustFind("t.lvl2");
    vpiHandle pickedh = mustFind("t.picked");
    if (errors) return 12;
    vpiHandle lvl0w[LVL0];
    for (int i = 0; i < LVL0; ++i) {
        lvl0w[i] = vpi_handle_by_index(lvl0h, i);
        if (!lvl0w[i]) {
            std::printf("%%Error: vpi_handle_by_index(t.lvl0, %0d) returned null\n", i);
            ++errors;
        } else if (vpi_get(vpiType, lvl0w[i]) != vpiMemoryWord
                   && vpi_get(vpiType, lvl0w[i]) != vpiReg) {
            std::printf("%%Error: t.lvl0[%0d] unexpected vpiType %0d\n", i,
                        vpi_get(vpiType, lvl0w[i]));
            ++errors;
        }
    }
    if (errors) return 13;

    int e0[LVL0], e1[4], e2[2], ep;
    const auto checkTree = [&](const char* why) {
        expectTree(0x77, 11, e0, e1, e2, ep);
        for (int i = 0; i < LVL0; ++i) {
            char nm[64];
            std::snprintf(nm, sizeof(nm), "t.lvl0[%0d] (%s)", i, why);
            checkInt(nm, lvl0w[i], e0[i]);
        }
        for (int i = 0; i < 4; ++i) {
            vpiHandle h = vpi_handle_by_index(lvl1h, i);
            checkInt("t.lvl1 word", h, e1[i]);
        }
        for (int i = 0; i < 2; ++i) {
            vpiHandle h = vpi_handle_by_index(lvl2h, i);
            checkInt("t.lvl2 word", h, e2[i]);
        }
        checkInt("t.picked (variable-index read of a reconstructed array)", pickedh, ep);
    };
    checkTree("element read");

    // Whole-array read of a reconstructed array.
    {
        s_vpi_arrayvalue av{};
        av.format = vpiIntVal;
        PLI_INT32 idx = 0;
        vpi_get_value_array(lvl0h, &av, &idx, LVL0);
        if (!av.value.integers) {
            std::printf("%%Error: vpi_get_value_array(t.lvl0) returned no data\n");
            ++errors;
        } else {
            for (int i = 0; i < LVL0; ++i) {
                if ((av.value.integers[i] & 0xff) != e0[i]) {
                    std::printf("%%Error: vpi_get_value_array t.lvl0[%0d] got %0d, want %0d\n", i,
                                av.value.integers[i] & 0xff, e0[i]);
                    ++errors;
                }
            }
        }
    }

    // Whole-array deposit into a reconstructed array.
    {
        s_vpi_arrayvalue av{};
        av.format = vpiIntVal;
        PLI_INT32 vals[LVL0];
        for (int i = 0; i < LVL0; ++i) vals[i] = 0x20 + i;
        av.value.integers = vals;
        PLI_INT32 idx = 0;
        vpi_put_value_array(lvl0h, &av, &idx, LVL0);
        for (int i = 0; i < LVL0; ++i) {
            char nm[64];
            std::snprintf(nm, sizeof(nm), "t.lvl0[%0d] (after vpi_put_value_array)", i);
            checkInt(nm, lvl0w[i], 0x20 + i);
        }
    }
    topp->we = 0;
    cycle();
    checkTree("recomputed after whole-array put");

    // A deposit into one element holds until the next eval recomputes it.
    putInt(lvl0w[3], 0x5a);
    checkInt("t.lvl0[3] (immediately after VPI put)", lvl0w[3], 0x5a);
    checkInt("t.lvl0[2] (unaffected by a sibling deposit)", lvl0w[2], e0[2]);
    topp->we = 0;
    cycle();
    checkTree("recomputed after eval");

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
