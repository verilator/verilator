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

#include "TestCheck.h"
#include "vpi_user.h"

#include <cstdio>
#include <fstream>
#include <string>

int errors = 0;

namespace {

// idmap.xml sits next to the running model binary, named "<binary>__idmap.xml";
// vpi_get_vlog_info() gives argv[0] since TEST_OBJ_DIR/VM_PREFIX aren't defined
// when this file is built as a separate PLI plugin.
std::string findIdmapPath() {
    s_vpi_vlog_info vlogInfo{};
    vpi_get_vlog_info(&vlogInfo);
    return std::string{vlogInfo.argv[0]} + "__idmap.xml";
}

// --protect-ids hashes non-top identifiers; recover 'realName's hash from idmap.xml.
std::string hashedName(const std::string& realName) {
    const std::string idmapPath = findIdmapPath();
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
    if (!handle) { TEST_CHECK_NZ_LABEL(name, handle); }
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

void checkProtected() {
    const std::string tHash = hashedName("t");
    const std::string cmbHash = hashedName("cmb");
    const std::string alias1Hash = hashedName("alias1");
    if (errors) return;

    const std::string cmbPath = tHash + "." + cmbHash;
    const std::string alias1Path = tHash + "." + alias1Hash;
    const vpiHandle cmbh = mustFind(cmbPath.c_str());
    const vpiHandle alias1h = mustFind(alias1Path.c_str());
    if (errors) return;

    checkInt(alias1Path.c_str(), alias1h, 0x2d);
    checkInt(cmbPath.c_str(), cmbh, 0x2e);
}

PLI_INT32 readOnlySynchCb(s_cb_data*) {
    checkProtected();
    return 0;
}

PLI_INT32 endOfSimCb(s_cb_data*) {
    if (!errors) std::printf("*-* All Finished *-*\n");
    return 0;
}

PLI_INT32 startOfSimCb(s_cb_data*) {
    s_vpi_time time = {vpiSimTime, 0, 0, 0};
    s_cb_data cb_data{};
    cb_data.reason = cbReadOnlySynch;
    cb_data.cb_rtn = readOnlySynchCb;
    cb_data.time = &time;
    const vpiHandle handle = vpi_register_cb(&cb_data);
    TEST_CHECK_NZ_LABEL("cbReadOnlySynch", handle);
    return 0;
}

void bootstrap() {
    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = startOfSimCb;
    vpi_register_cb(&cb_data);

    cb_data.reason = cbEndOfSimulation;
    cb_data.cb_rtn = endOfSimCb;
    vpi_register_cb(&cb_data);
}

}  // namespace

void (*vlog_startup_routines[])() = {bootstrap, 0};
