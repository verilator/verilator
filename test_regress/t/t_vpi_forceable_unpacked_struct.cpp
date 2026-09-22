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

#include "verilated.h"

#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"
#include "sv_vpi_user.h"
#include "vpi_user.h"

#include <string>
#include <unordered_set>

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

bool expectForceable(vpiHandle handle) {
    putValue(handle, 1, vpiForceFlag);
    s_vpi_error_info error{};
    if (!vpi_chk_error(&error) || !error.message) return true;
    return std::string{error.message}.find("non-forceable") == std::string::npos;
}

int errors = 0;

bool mon_check() {

    TestVpiHandle forceable_response
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("t.forceable_response"), nullptr);
    TEST_CHECK_NZ(forceable_response);
    if (errors) return true;

    std::unordered_set<std::string> discoverable_by_iterate;
    if (TestVpiHandle members = vpi_iterate(vpiMember, forceable_response)) {
        while (TestVpiHandle member = vpi_scan(members)) {
            discoverable_by_iterate.insert(vpi_get_str(vpiFullName, member));
        }
        members.freed();
    }
    const std::unordered_set<std::string> expected_members
        = {"t.forceable_response.a", "t.forceable_response.b", "t.forceable_response.nested"};
    TEST_CHECK(discoverable_by_iterate.size(), expected_members.size(),
               discoverable_by_iterate == expected_members);

    TestVpiHandle a = vpi_handle_by_name(const_cast<PLI_BYTE8*>("a"), forceable_response);
    TestVpiHandle b = vpi_handle_by_name(const_cast<PLI_BYTE8*>("b"), forceable_response);
    TestVpiHandle nested
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("nested"), forceable_response);
    TestVpiHandle c
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>("t.forceable_response.nested.c"), nullptr);
    TEST_CHECK_NZ(a);
    TEST_CHECK_NZ(b);
    TEST_CHECK_NZ(nested);
    TEST_CHECK_NZ(c);
    if (errors) return true;

    std::unordered_set<std::string> nested_members;
    if (TestVpiHandle members = vpi_iterate(vpiMember, nested)) {
        while (TestVpiHandle member = vpi_scan(members)) {
            nested_members.insert(vpi_get_str(vpiFullName, member));
        }
        members.freed();
    }
    const std::unordered_set<std::string> expected_nested_members
        = {"t.forceable_response.nested.c"};
    TEST_CHECK(nested_members.size(), expected_nested_members.size(),
               nested_members == expected_nested_members);

    TEST_CHECK_EQ(vpi_get(vpiSize, a), 32);
    TEST_CHECK_EQ(vpi_get(vpiSize, b), 16);
    TEST_CHECK_EQ(vpi_get(vpiSize, c), 8);

    TEST_CHECK_NZ(putValue(a, 11));
    TEST_CHECK_NZ(putValue(b, 22));
    TEST_CHECK_NZ(putValue(c, 33));
    TEST_CHECK_EQ(getValue(a), 11);
    TEST_CHECK_EQ(getValue(b), 22);
    TEST_CHECK_EQ(getValue(c), 33);
    return errors;
}

PLI_INT32 value_change(t_cb_data* datap) {
    // Some simulators also report the declaration initializer as a change;
    // only the write in the initial block, which sets it, means run now
    if (!datap->value || !datap->value->value.integer) return 0;
    if (mon_check()) vpi_control(vpiStop);
    return 0;
}

std::string test_top() {
    std::string top;
#ifdef TEST_MODEL_NAME
    top = std::string{TEST_STRINGIFY(TEST_MODEL_NAME)} + ".";
#endif
    top += TestSimulator::top();
    return top;
}

void check_failed(const std::string& msg) { std::cout << "%Error: " << msg << std::endl; }

PLI_INT32 start_of_sim(t_cb_data* /*datap*/) {
    const std::string watched = test_top() + ".run_mon_check";
    TestVpiHandle varh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(watched.c_str()), NULL);
    if (!varh) {
        check_failed("vpi_handle_by_name('" + watched + "') = NULL");
        vpi_control(vpiStop);
        return 0;
    }

    static s_vpi_time vpi_time;
    vpi_time.type = vpiSuppressTime;
    static s_vpi_value vpi_value;
    vpi_value.format = vpiIntVal;

    static s_cb_data cb_data{};
    cb_data.reason = cbValueChange;
    cb_data.cb_rtn = &value_change;
    cb_data.obj = varh;
    cb_data.time = &vpi_time;
    cb_data.value = &vpi_value;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
    varh.freed();  // Callback holds it
    return 0;
}

void vpi_compat_bootstrap() {
    static s_vpi_time vpi_time;
    vpi_time.high = 0;
    vpi_time.low = 0;
    vpi_time.type = vpiSimTime;

    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    cb_data.obj = NULL;
    cb_data.time = &vpi_time;
    cb_data.value = NULL;
    cb_data.index = 0;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

}  // namespace

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, nullptr};
