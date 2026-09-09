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

#include "Vt_vpi_lazy_emit.h"
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

int boundVal(vpiHandle handle, PLI_INT32 relation) {
    vpiHandle bound = vpi_handle(relation, handle);
    if (!bound) return -777;
    return readInt(bound);
}

void checkProp(const char* name, PLI_INT32 got, PLI_INT32 expected, const char* what) {
    if (got != expected) {
        std::printf("%%Error: %s %s expected %0d, got %0d\n", name, what, expected, got);
        ++errors;
    }
}

void checkVpiProp(const char* name, vpiHandle handle, PLI_INT32 prop, int expected) {
    const int got = vpi_get(prop, handle);
    if (got != expected) {
        std::printf("%%Error: %s expected %0d, got %0d\n", name, expected, got);
        ++errors;
    }
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_emit> topp{new Vt_vpi_lazy_emit{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

    topp->rst = 1;
    topp->clk = 0;
    topp->a = 0;
    topp->in_a = 0;
    topp->in_b = 0;
    topp->in_signed = 0;
    topp->in_enum = 0;
    topp->in_int = 0;
    topp->in_unsigned = 0;
    topp->in_logic = 0;
    topp->eval();
    cycle();
    topp->rst = 0;

    // aliasmeta
    {
        topp->in_a = 0xa5;
        topp->in_b = 0x3c;
        cycle();  // src_a <= 0xa5, src_b <= 0x3c

        vpiHandle aWide = mustFind("t.a_wide");
        vpiHandle aNet = mustFind("t.a_net");
        if (errors) return 10;

        // a_wide is declared [8:1] over a [7:0] canonical, so the row must report the
        // alias's own bounds
        checkProp("t.a_wide", boundVal(aWide, vpiLeftRange), 8, "vpiLeftRange");
        checkProp("t.a_wide", boundVal(aWide, vpiRightRange), 1, "vpiRightRange");
        checkProp("t.a_wide", vpi_get(vpiSize, aWide), 8, "vpiSize");

        // a_net keeps its own [7:0] bounds
        checkProp("t.a_net", boundVal(aNet, vpiLeftRange), 7, "vpiLeftRange");
        checkProp("t.a_net", boundVal(aNet, vpiRightRange), 0, "vpiRightRange");
        checkProp("t.a_net", vpi_get(vpiSize, aNet), 8, "vpiSize");

        // Value still tracks the canonical
        checkInt("t.a_wide", aWide, 0xa5);
        checkInt("t.a_net", aNet, 0x3c);
    }

    // alias_dtype
    {
        vpiHandle aSign = mustFind("t.a_sign");
        vpiHandle aEnum = mustFind("t.a_enum");
        vpiHandle aInt = mustFind("t.a_ii");
        vpiHandle aSSign = mustFind("t.a_ssign");
        vpiHandle aBit = mustFind("t.a_bit");
        vpiHandle signedSrc = mustFind("t.signed_src");
        vpiHandle enumVar = mustFind("t.enum_var");
        vpiHandle integerVar = mustFind("t.integer_var");
        vpiHandle unsignedSrc = mustFind("t.unsigned_src");
        vpiHandle logicSrc = mustFind("t.logic_src");
        vpiHandle combSrcH = mustFind("t.comb_src");
        vpiHandle aSame = mustFind("t.a_same");
        vpiHandle aDiff = mustFind("t.a_diff");
        vpiHandle coneSame = mustFind("t.cone_same");
        vpiHandle coneDiff = mustFind("t.cone_diff");
        if (errors) return 10;

        checkVpiProp("t.a_sign vpiSigned", aSign, vpiSigned, 0);  // declared unsigned
        checkVpiProp("t.signed_src vpiSigned", signedSrc, vpiSigned, 1);  // canonical signed
        checkVpiProp("t.a_ssign vpiSigned", aSSign, vpiSigned, 1);  // declared signed
        checkVpiProp("t.unsigned_src vpiSigned", unsignedSrc, vpiSigned, 0);  // canonical unsigned
        checkVpiProp("t.a_bit vpiType", aBit, vpiType, vpiBitVar);  // declared 'bit'
        checkVpiProp("t.logic_src vpiType", logicSrc, vpiType, vpiReg);  // canonical 4-state
        checkVpiProp("t.a_enum vpiType", aEnum, vpiType, vpiReg);  // declared 'logic'

        struct Vec {  // vpiIntVal = raw bits (no sign extension)
            int inSigned;
            int inEnum;
            int inInt;
            int inUnsigned;
            int inLogic;
            int expSign;
            int expEnum;
            int expInt;
            int expUnsigned;
            int expLogic;
        };
        const Vec vecs[] = {
            {-16, 200, -12345, 0xA5, 0x3C, 0xF0, 200, -12345, 0xA5, 0x3C},
            {100, 10, 0x12345678, 0x7F, 0x81, 100, 10, 0x12345678, 0x7F, 0x81},
            {-1, 100, -1, 0x00, 0xFF, 0xFF, 100, -1, 0x00, 0xFF},
        };

        for (const Vec& v : vecs) {
            topp->in_signed = v.inSigned;
            topp->in_enum = v.inEnum;
            topp->in_int = v.inInt;
            topp->in_unsigned = v.inUnsigned;
            topp->in_logic = v.inLogic;
            cycle();

            checkInt("t.a_sign", aSign, v.expSign);
            checkInt("t.a_enum", aEnum, v.expEnum);
            checkInt("t.a_ii", aInt, v.expInt);
            checkInt("t.a_ssign", aSSign, v.expUnsigned);
            checkInt("t.a_bit", aBit, v.expLogic);

            checkInt("t.a_sign vs signed_src", aSign, readInt(signedSrc));
            checkInt("t.a_enum vs enum_var", aEnum, readInt(enumVar));
            checkInt("t.a_ii vs integer_var", aInt, readInt(integerVar));
            checkInt("t.a_ssign vs unsigned_src", aSSign, readInt(unsignedSrc));
            checkInt("t.a_bit vs logic_src", aBit, readInt(logicSrc));

            // Both alias the reconstructed t.comb_src; only a_same can be substituted into
            // its cone, a_diff differing in sign is pinned with storage of its own
            const int combSrc = (v.expUnsigned ^ 0x3c) & 0xff;
            checkInt("t.comb_src", combSrcH, combSrc);
            checkInt("t.a_same", aSame, combSrc);
            checkInt("t.cone_same", coneSame, combSrc ^ 0x5a);
            checkInt("t.a_diff", aDiff, combSrc);
            checkInt("t.cone_diff", coneDiff, combSrc ^ 0x5a);
        }

        // signed_src is a flop, so a_sign is retained with its own storage: the deposit is
        // confined to the alias and the driver re-asserts on the next eval
        const int signedSrcPre = readInt(signedSrc);
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x5a;
        if (!vpi_put_value(aSign, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write through alias t.a_sign\n");
            ++errors;
        }
        checkInt("t.a_sign (deposit)", aSign, 0x5a);
        checkInt("t.signed_src (unchanged by a_sign put)", signedSrc, signedSrcPre);
        topp->eval();
        checkInt("t.a_sign (settle re-run)", aSign, signedSrcPre);
        checkInt("t.signed_src (unchanged by settle)", signedSrc, signedSrcPre);
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
