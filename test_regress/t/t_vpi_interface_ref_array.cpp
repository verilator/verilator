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

// Interface references must be discoverable by iteration, not only by name.
// A tool that does not know the port names walks vpiInternalScope children;
// an array port "arr[12]" has no object named "arr", so its elements are only
// reachable that way.  Foo is a leaf module with no child scopes, which is the
// case that used to produce no iterator at all. Twelve elements exercise
// multi-digit indices; discovery must not depend on numeric iteration order.

#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

#include <string>
#include <utility>
#include <vector>

int errors = 0;

static std::string str_of(vpiHandle h, PLI_INT32 prop) {
    const char* const got = vpi_get_str(prop, h);
    TEST_CHECK_NZ(got);
    return got ? got : "<null>";
}

// Iterate vpiInternalScope, returning the (type, fullname) of each child
static std::vector<std::pair<PLI_INT32, std::string>> children_of(vpiHandle scope,
                                                                  const std::string& what) {
    std::vector<std::pair<PLI_INT32, std::string>> out;
    TestVpiHandle it = vpi_iterate(vpiInternalScope, scope);
    TEST_CHECK_NZ_LABEL(what, it);
    if (!it) return out;
    TEST_CHECK_EQ(vpi_get(vpiType, it), vpiIterator);
    while (TestVpiHandle h = vpi_scan(it)) {
        out.emplace_back(vpi_get(vpiType, h), str_of(h, vpiFullName));
        const std::string& fullname = out.back().second;
        TEST_CHECK_EQ_LABEL(fullname, str_of(h, vpiName),
                            fullname.substr(fullname.rfind('.') + 1));
    }
    it.freed();  // vpi_scan at end released it
    return out;
}

static void check_child(const std::vector<std::pair<PLI_INT32, std::string>>& children,
                        PLI_INT32 type, const std::string& fullname) {
    int n = 0;
    for (const auto& child : children) {
        if (child.first == type && child.second == fullname) ++n;
    }
    TEST_CHECK_EQ_LABEL(fullname, n, 1);
}

// Follow a reference to its concrete interface, checking each step's name
static void check_actual(const std::string& refName, bool modport, const std::string& concrete) {
    const TestVpiHandle refh
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(refName.c_str()), nullptr);
    TEST_CHECK_NZ_LABEL(refName, refh);
    if (!refh) return;
    TEST_CHECK_EQ_LABEL(refName, vpi_get(vpiType, refh), vpiRefObj);
    const TestVpiHandle actualh = vpi_handle(vpiActual, refh);
    TEST_CHECK_NZ_LABEL(refName, actualh);
    if (!actualh) return;
    if (modport) {
        TEST_CHECK_EQ_LABEL(refName, vpi_get(vpiType, actualh), vpiModport);
        TEST_CHECK_EQ_LABEL(refName, str_of(actualh, vpiFullName), concrete + ".SomeModport");
        const TestVpiHandle intfh = vpi_handle(vpiInterface, actualh);
        TEST_CHECK_NZ_LABEL(refName, intfh);
        if (!intfh) return;
        TEST_CHECK_EQ_LABEL(refName, vpi_get(vpiType, intfh), vpiInterface);
        TEST_CHECK_EQ_LABEL(refName, str_of(intfh, vpiFullName), concrete);
    } else {
        TEST_CHECK_EQ_LABEL(refName, vpi_get(vpiType, actualh), vpiInterface);
        TEST_CHECK_EQ_LABEL(refName, str_of(actualh, vpiFullName), concrete);
    }
}

static void check_all() {
    const std::string top = TestSimulator::top();
    const std::string foo = top + ".foo";

    // Root iteration includes modules, but skips packages and has no reference vector.
    {
        const auto children = children_of(nullptr, "root");
        check_child(children, vpiModule, top);
        TEST_CHECK_EQ(children.size(), 1);
        const TestVpiHandle package
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>("RefPackage"), nullptr);
        TEST_CHECK_NZ(package);
        if (package) TEST_CHECK_EQ(vpi_get(vpiType, package), vpiPackage);
    }

    // The leaf module yields exactly its thirteen references, and nothing else
    {
        const TestVpiHandle fooh
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(foo.c_str()), nullptr);
        TEST_CHECK_NZ_LABEL(foo, fooh);
        if (fooh) {
            const auto children = children_of(fooh, foo);
            for (int i = 0; i < 12; ++i) {
                check_child(children, vpiRefObj, foo + ".arr[" + std::to_string(i) + "]");
            }
            check_child(children, vpiRefObj, foo + ".plain");
            TEST_CHECK_EQ_LABEL(foo, children.size(), 13);
        }
    }

    // The top yields its child scopes but no references, as it declares none
    {
        const TestVpiHandle toph
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(top.c_str()), nullptr);
        TEST_CHECK_NZ_LABEL(top, toph);
        if (toph) {
            const auto children = children_of(toph, top);
            check_child(children, vpiModule, foo);
            for (int i = 0; i < 12; ++i) {
                check_child(children, vpiInterface, top + ".top_arr[" + std::to_string(i) + "]");
            }
            check_child(children, vpiInterface, top + ".top_plain");
            for (const auto& child : children) { TEST_CHECK_NE(child.first, vpiRefObj); }
        }
    }

    for (int i = 0; i < 12; ++i) {
        check_actual(foo + ".arr[" + std::to_string(i) + "]", true,
                     top + ".top_arr[" + std::to_string(i) + "]");
    }
    check_actual(foo + ".plain", false, top + ".top_plain");

    // Nothing is named after the array itself; the tool builds that from the elements
    const std::string arr = foo + ".arr";
    const TestVpiHandle arrh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(arr.c_str()), nullptr);
    TEST_CHECK_Z(arrh);
}

static PLI_INT32 start_of_sim(t_cb_data* /*datap*/) {
    check_all();
    if (errors) vpi_control(vpiStop);
    return 0;
}

void vpi_compat_bootstrap() {
    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, nullptr};
