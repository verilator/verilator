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
#include "TestVpi.h"
#include "vpi_user.h"

#include <cstdio>
#include <fstream>
#include <string>

int errors = 0;

namespace {

// --protect-ids hashes non-top identifiers; recover 'realName's hash from the idmap.xml
// that sits next to the model binary, as TEST_OBJ_DIR is not defined for a PLI plugin
std::string hashedName(const std::string& realName) {
    s_vpi_vlog_info vlogInfo{};
    vpi_get_vlog_info(&vlogInfo);
    const std::string idmapPath = std::string{vlogInfo.argv[0]} + "__idmap.xml";
    std::ifstream idmap{idmapPath};
    if (!idmap) {
        std::printf("%%Error: %s:%d: failed to open %s\n", __FILE__, __LINE__, idmapPath.c_str());
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
    std::printf("%%Error: %s:%d: no idmap entry for '%s'\n", __FILE__, __LINE__, realName.c_str());
    ++errors;
    return "";
}

void checkInt(const std::string& name, int expected) {
    TestVpiHandle handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name.c_str()), nullptr);
    TEST_CHECK_NZ_LABEL(name, handle);
    if (!handle) return;
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    TEST_CHECK_EQ_LABEL(name, value.value.integer, expected);
}

PLI_INT32 readOnlySynchCb(s_cb_data*) {
    const std::string tHash = hashedName("t");
    checkInt(tHash + "." + hashedName("alias1"), 0x2d);
    checkInt(tHash + "." + hashedName("cmb"), 0x2e);
    if (errors) vpi_control(vpiStop, 1);
    return 0;
}

void bootstrap() {
    s_vpi_time time = {vpiSimTime, 0, 0, 0};
    s_cb_data cb_data{};
    cb_data.reason = cbReadOnlySynch;
    cb_data.cb_rtn = readOnlySynchCb;
    cb_data.time = &time;
    TestVpiHandle handle = vpi_register_cb(&cb_data);
    TEST_CHECK_NZ_LABEL("cbReadOnlySynch", handle);
}

}  // namespace

void (*vlog_startup_routines[])() = {bootstrap, 0};
