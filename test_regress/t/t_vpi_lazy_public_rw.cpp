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

#include "Vt_vpi_lazy_public_rw.h"
#include "vpi_user.h"

#include <cstdio>
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

// cbValueChange bookkeeping for a reconstructed signal.
int cmb1CbCount = 0;
int cmb1CbLast = -1;
PLI_INT32 cmb1Cb(p_cb_data cb_data) {
    ++cmb1CbCount;
    cmb1CbLast = cb_data->value->value.integer;
    return 0;
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw> topp{
        new Vt_vpi_lazy_public_rw{contextp.get(), ""}};

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

    // Reset
    topp->rst = 1;
    topp->clk = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    int keep = 0;
    const auto cmb1Of = [](int k) { return (k + 0x7) & 0x7f; };
    const auto cmb2Of = [](int k) { return (((k + 0x7) & 0x7f) ^ 0x2a) & 0x7f; };
    const auto cmb3Of
        = [](int k) { return ((((((k + 0x7) & 0x7f) ^ 0x2a) & 0x7f) + 0x5)) & 0x7f; };

    vpiHandle cmb1 = mustFind("t.cmb1");
    vpiHandle cmb2 = mustFind("t.cmb2");
    vpiHandle cmb3 = mustFind("t.cmb3");
    vpiHandle keeph = mustFind("t.keep");
    vpiHandle observe = mustFind("observe");
    vpiHandle alias1 = mustFind("t.alias1");
    vpiHandle alias2 = mustFind("t.alias2");
    vpiHandle portIn = mustFind("t.u_sub.port_in");
    vpiHandle portOut = mustFind("t.u_sub.port_out");
    if (errors) return 10;

    for (int i = 0; i < 4; ++i) {
        cycle();
        keep = (keep + 0x3) & 0x7f;
        checkInt("t.keep", keeph, keep);
        checkInt("t.cmb1", cmb1, cmb1Of(keep));
        checkInt("t.cmb2", cmb2, cmb2Of(keep));
        checkInt("t.cmb3", cmb3, cmb3Of(keep));
        checkInt("t.alias1", alias1, keep);
        checkInt("t.alias2", alias2, keep);
        checkInt("t.u_sub.port_in", portIn, keep);
        checkInt("t.u_sub.port_out", portOut, keep);
    }

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

    const int cbCountBefore = cmb1CbCount;
    cycle();
    keep = (keep + 0x3) & 0x7f;
    if (cmb1CbCount <= cbCountBefore) {
        std::printf("%%Error: cbValueChange on reconstructed t.cmb1 did not fire\n");
        ++errors;
    }
    if (cmb1CbLast != cmb1Of(keep)) {
        std::printf("%%Error: cbValueChange delivered %0d, expected %0d\n", cmb1CbLast,
                    cmb1Of(keep));
        ++errors;
    }

    // Reconstructed signal is read-only.
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
    checkInt("t.cmb2", cmb2, cmb2Of(keep));
    Verilated::fatalOnVpiError(true);

    wr.value.integer = 0x20;
    if (!vpi_put_value(keeph, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write boundary signal t.keep\n");
        ++errors;
    }
    checkInt("t.keep (after put)", keeph, 0x20);
    keep = 0x20;
    checkInt("t.cmb1 (after put)", cmb1, cmb1Of(keep));

    // Write alias -> updates canonical storage.
    wr.value.integer = 0x33;
    if (!vpi_put_value(alias2, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through alias t.alias2\n");
        ++errors;
    }
    keep = 0x33;
    checkInt("t.keep (via alias2 put)", keeph, keep);
    checkInt("t.alias1 (via alias2 put)", alias1, keep);
    checkInt("t.u_sub.port_in (via alias2 put)", portIn, keep);
    checkInt("t.u_sub.port_out (via alias2 put)", portOut, keep);

    wr.value.integer = 0x15;
    if (!vpi_put_value(portOut, &wr, nullptr, vpiNoDelay)) {
        std::printf("%%Error: failed to write through inlined port t.u_sub.port_out\n");
        ++errors;
    }
    keep = 0x15;
    checkInt("t.keep (via port_out put)", keeph, keep);
    checkInt("t.alias2 (via port_out put)", alias2, keep);

    cycle();
    keep = (keep + 0x3) & 0x7f;
    checkInt("t.keep (after eval)", keeph, keep);
    checkInt("t.alias1 (after eval)", alias1, keep);
    checkInt("t.cmb3 (after eval)", cmb3, cmb3Of(keep));

    vpiHandle deadh = mustFind("t.dead");
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
        checkInt("t.dead (clocked overwrite)", deadh, (prevKeep + 0x9) & 0x7f);
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
