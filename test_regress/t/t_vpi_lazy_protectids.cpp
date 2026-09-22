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

#include "vpi_user.h"

#include "TestCheck.h"

#include <cstdio>
#include <fstream>
#include <string>

int errors = 0;

namespace {

// --protect-ids hashes non-top identifiers; recover 'realName's hash from idmap.xml.
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
        const std::string rooted = std::string{"top."} + name;
        handle = vpi_handle_by_name((PLI_BYTE8*)rooted.c_str(), nullptr);
    }
    if (!handle) {
        TEST_CHECK_NZ_LABEL(name, handle);
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
    TEST_CHECK_EQ_LABEL(name, got, expected);
}

}  // namespace

// Under --protect-ids VPI names are obfuscated; compile+run proves the symbol table works.
extern "C" int vpi_lazy_protectids_check() {
    const std::string tHash = hashedName("t");
    const std::string cmbHash = hashedName("cmb");
    const std::string alias1Hash = hashedName("alias1");
    if (errors) return 1;

    const std::string cmbPath = tHash + "." + cmbHash;
    const std::string alias1Path = tHash + "." + alias1Hash;
    vpiHandle cmbh = mustFind(cmbPath.c_str());
    vpiHandle alias1h = mustFind(alias1Path.c_str());
    if (errors) return 1;

    checkInt(alias1Path.c_str(), alias1h, 0x2d);
    checkInt(cmbPath.c_str(), cmbh, 0x2e);
    return errors ? 1 : 0;
}
