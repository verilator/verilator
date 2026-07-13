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

#include "Vt_vpi_lazy_public_rw_protectids.h"
#include "vpi_user.h"

#include <cstdio>
#include <fstream>
#include <memory>
#include <string>

namespace {

int errors = 0;

// --protect-ids hashes every non-top-level identifier; recover the runtime
// hash for 'realName' from the idmap.xml Verilator emits alongside the model.
std::string hashedName(const std::string& realName) {
    const std::string idmapPath
        = std::string(VL_STRINGIFY(TEST_OBJ_DIR)) + "/" + VL_STRINGIFY(VM_PREFIX) + "__idmap.xml";
    std::ifstream idmap{idmapPath};
    if (!idmap) {
        std::printf("%%Error: failed to open %s\n", idmapPath.c_str());
        ++errors;
        return "";
    }
    const std::string needle = "to=\"" + realName + "\"";
    std::string line;
    while (std::getline(idmap, line)) {
        if (line.find(needle) == std::string::npos) continue;
        const std::string::size_type fromPos = line.find("from=\"");
        if (fromPos == std::string::npos) continue;
        const std::string::size_type start = fromPos + 6;
        const std::string::size_type end = line.find('"', start);
        if (end == std::string::npos) continue;
        return line.substr(start, end - start);
    }
    std::printf("%%Error: no idmap entry for '%s'\n", realName.c_str());
    ++errors;
    return "";
}

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

}  // namespace

// Under --protect-ids VPI names are obfuscated; compile+run proves symbol table works.
int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vt_vpi_lazy_public_rw_protectids> topp{
        new Vt_vpi_lazy_public_rw_protectids{contextp.get(), ""}};

    const std::string tHash = hashedName("t");
    const std::string cmbHash = hashedName("cmb");
    const std::string alias1Hash = hashedName("alias1");
    if (errors) return 10;

    const std::string cmbPath = tHash + "." + cmbHash;
    const std::string alias1Path = tHash + "." + alias1Hash;
    vpiHandle cmbh = mustFind(cmbPath.c_str());
    vpiHandle alias1h = mustFind(alias1Path.c_str());
    if (errors) return 10;

    topp->rst = 1;
    topp->clk = 0;
    topp->eval();

    int keep = 0;
    const auto cmbOf = [](int k) { return (k + 0x1) & 0x7f; };

    for (int i = 0; i < 5; ++i) {
        topp->clk = 0;
        topp->eval();
        topp->clk = 1;
        topp->eval();
        topp->rst = 0;
        VerilatedVpi::callValueCbs();
        if (i > 0) keep = (keep + 0x3) & 0x7f;
        checkInt(alias1Path.c_str(), alias1h, keep);
        checkInt(cmbPath.c_str(), cmbh, cmbOf(keep));
    }

    topp->final();
    if (errors) {
        std::printf("%%Error: %0d failures\n", errors);
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
