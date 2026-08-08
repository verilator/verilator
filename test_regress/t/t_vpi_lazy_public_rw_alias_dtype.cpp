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

#include "Vt_vpi_lazy_public_rw_alias_dtype.h"
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

void checkProp(const char* name, vpiHandle handle, PLI_INT32 prop, int expected) {
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

    const std::unique_ptr<Vt_vpi_lazy_public_rw_alias_dtype> topp{
        new Vt_vpi_lazy_public_rw_alias_dtype{contextp.get(), ""}};

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
    if (errors) return 10;

    checkProp("t.a_sign vpiSigned", aSign, vpiSigned, 0);  // declared unsigned
    checkProp("t.signed_src vpiSigned", signedSrc, vpiSigned, 1);  // canonical is signed
    checkProp("t.a_ssign vpiSigned", aSSign, vpiSigned, 1);  // declared signed
    checkProp("t.unsigned_src vpiSigned", unsignedSrc, vpiSigned, 0);  // canonical is unsigned
    checkProp("t.a_bit vpiType", aBit, vpiType, vpiBitVar);  // declared 'bit'
    checkProp("t.logic_src vpiType", logicSrc, vpiType, vpiReg);  // canonical is 4-state
    checkProp("t.a_enum vpiType", aEnum, vpiType, vpiReg);  // declared 'logic'

    const auto cycle = [&]() {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
    };

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
    }

    {
        s_vpi_value wr{};
        wr.format = vpiIntVal;
        wr.value.integer = 0x5a;
        if (!vpi_put_value(aSign, &wr, nullptr, vpiNoDelay)) {
            std::printf("%%Error: failed to write through alias t.a_sign\n");
            ++errors;
        }
        checkInt("t.a_sign (after put)", aSign, 0x5a);
        checkInt("t.signed_src (via a_sign put)", signedSrc, 0x5a);
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
