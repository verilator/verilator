// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include VM_PREFIX_INCLUDE

#include "verilated.h"

#include "TestVpi.h"
#include "sv_vpi_user.h"
#include "vpi_user.h"

#include <iostream>
#include <string>
#include <unordered_set>

using std::string_literals::operator""s;

namespace {

bool putValue(vpiHandle handle, PLI_INT32 val, PLI_INT32 flags = vpiNoDelay) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    value.value.integer = val;
    return vpi_put_value(handle, &value, nullptr, flags);
}

PLI_INT32 getValue(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return value.value.integer;
}

bool expectNotForceable(vpiHandle handle, const std::string& fullName) {
    if (putValue(handle, 1, vpiForceFlag)) return false;
    s_vpi_error_info error{};
    if (!vpi_chk_error(&error) || !error.message) return false;
    return std::string{error.message}
           == "vpi_put_value used with vpiForceFlag on non-forceable signal '" + fullName + "'";
}

}  // namespace

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    contextp->fatalOnVpiError(false);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};
    topp->eval();

    TestVpiHandle forceable_response
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("top.forceable_response"), nullptr);
    if (!forceable_response) {
        std::cerr << "'forceable_response' not discoverable\n";
        return 1;
    }

    std::unordered_set<std::string> discoverable_by_iterate;
    if (TestVpiHandle members = vpi_iterate(vpiMember, forceable_response)) {
        while (TestVpiHandle member = vpi_scan(members)) {
            discoverable_by_iterate.insert(vpi_get_str(vpiFullName, member));
        }
        members.freed();
    }
    if (discoverable_by_iterate.find("top.forceable_response.a"s) == discoverable_by_iterate.end()
        || discoverable_by_iterate.find("top.forceable_response.b"s)
               == discoverable_by_iterate.end()
        || discoverable_by_iterate.find("top.forceable_response.nested"s)
               == discoverable_by_iterate.end()) {
        std::cerr << "Signals not discoverable by 'vpi_iterate'\n";
        return 1;
    }

    TestVpiHandle a = vpi_handle_by_name(const_cast<PLI_BYTE8*>("a"), forceable_response);
    TestVpiHandle b = vpi_handle_by_name(const_cast<PLI_BYTE8*>("b"), forceable_response);
    TestVpiHandle nested
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("nested"), forceable_response);
    TestVpiHandle c
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("top.forceable_response.nested.c"), nullptr);
    if (!a || !b || !nested || !c) {
        std::cerr << "Signals not discoverable by 'vpi_handle_by_name'\n";
        return 1;
    }

    std::unordered_set<std::string> nested_members;
    if (TestVpiHandle members = vpi_iterate(vpiMember, nested)) {
        while (TestVpiHandle member = vpi_scan(members)) {
            nested_members.insert(vpi_get_str(vpiFullName, member));
        }
        members.freed();
    }
    if (nested_members.find("top.forceable_response.nested.c"s) == nested_members.end()) {
        std::cerr << "Nested signal not discoverable by 'vpi_iterate'\n";
        return 1;
    }

    if (!putValue(a, 11) || !putValue(b, 22) || !putValue(c, 33) || getValue(a) != 11
        || getValue(b) != 22 || getValue(c) != 33) {
        std::cerr << "Member deposit failed\n";
        return 1;
    }

    if (!expectNotForceable(a, "top.forceable_response.a")) {
        std::cerr << "Struct member unexpectedly forceable\n";
        return 1;
    }

    return 0;
}
