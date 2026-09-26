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
// an array port "arr[4]" has no object named "arr", so its elements are only
// reachable that way.  Foo is a leaf module with no child scopes, which is the
// case that used to produce no iterator at all.
//
// The model is constructed, destroyed and constructed again in the same
// context before checking, so any reference left registered by the first
// model would show up as a duplicate.

#ifdef IS_VPI

#include "vpi_user.h"

#else

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE

#endif

#include <algorithm>
#include <cstring>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

static int errors = 0;

static void check_failed(const std::string& msg) {
    std::cout << "%Error: " << msg << std::endl;
    ++errors;
}

static std::string str_of(vpiHandle h, PLI_INT32 prop) {
    const char* const got = vpi_get_str(prop, h);
    return got ? got : "<null>";
}

static void check_str(vpiHandle h, PLI_INT32 prop, const std::string& what,
                      const std::string& expected) {
    const std::string got = str_of(h, prop);
    if (got != expected) {
        check_failed("vpi_get_str(" + std::string{prop == vpiName ? "vpiName" : "vpiFullName"}
                     + ", " + what + ") = '" + got + "', expected '" + expected + "'");
    }
}

static void check_type(vpiHandle h, const std::string& what, PLI_INT32 expected) {
    const PLI_INT32 got = vpi_get(vpiType, h);
    if (got != expected) {
        check_failed("vpi_get(vpiType, " + what + ") = " + strFromVpiObjType(got) + ", expected "
                     + strFromVpiObjType(expected));
    }
}

// Iterate vpiInternalScope, returning the (type, fullname) of each child
static std::vector<std::pair<PLI_INT32, std::string>> children_of(vpiHandle scope,
                                                                  const std::string& what) {
    std::vector<std::pair<PLI_INT32, std::string>> out;
    TestVpiHandle it = vpi_iterate(vpiInternalScope, scope);
    if (!it) {
        check_failed("vpi_iterate(vpiInternalScope, <" + what + ">) = NULL");
        return out;
    }
    while (vpiHandle h = vpi_scan(it)) {
        out.emplace_back(vpi_get(vpiType, h), str_of(h, vpiFullName));
        vpi_release_handle(h);
    }
    it.freed();  // vpi_scan at end released it
    return out;
}

static void check_child(const std::vector<std::pair<PLI_INT32, std::string>>& children,
                        const std::string& what, PLI_INT32 type, const std::string& fullname) {
    int n = 0;
    for (const auto& child : children) {
        if (child.first == type && child.second == fullname) ++n;
    }
    if (n != 1) {
        check_failed("vpi_iterate(vpiInternalScope, <" + what + ">) yielded "
                     + strFromVpiObjType(type) + " '" + fullname + "' " + std::to_string(n)
                     + " times, expected once");
    }
}

// Follow a reference to its concrete interface, checking each step's name
static void check_actual(const std::string& refName, bool modport, const std::string& concrete) {
    const TestVpiHandle refh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(refName.c_str()), NULL);
    if (!refh) {
        check_failed("vpi_handle_by_name('" + refName + "') = NULL");
        return;
    }
    check_type(refh, "'" + refName + "'", vpiRefObj);
    TestVpiHandle actualh = vpi_handle(vpiActual, refh);
    if (!actualh) {
        check_failed("vpi_handle(vpiActual, '" + refName + "') = NULL");
        return;
    }
    const std::string actWhat = "vpiActual of '" + refName + "'";
    if (modport) {
        check_type(actualh, actWhat, vpiModport);
        check_str(actualh, vpiFullName, actWhat, concrete + ".SomeModport");
        const TestVpiHandle intfh = vpi_handle(vpiInterface, actualh);
        if (!intfh) {
            check_failed("vpi_handle(vpiInterface, " + actWhat + ") = NULL");
            return;
        }
        check_type(intfh, "vpiInterface of " + actWhat, vpiInterface);
        check_str(intfh, vpiFullName, "vpiInterface of " + actWhat, concrete);
    } else {
        check_type(actualh, actWhat, vpiInterface);
        check_str(actualh, vpiFullName, actWhat, concrete);
    }
}

static void check_all() {
    const std::string top = TestSimulator::top();
    const std::string foo = top + ".foo";

    // The leaf module yields exactly its five references, and nothing else
    {
        const TestVpiHandle fooh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(foo.c_str()), NULL);
        if (!fooh) {
            check_failed("vpi_handle_by_name('" + foo + "') = NULL");
        } else {
            const auto children = children_of(fooh, foo);
            for (int i = 0; i < 4; ++i) {
                check_child(children, foo, vpiRefObj, foo + ".arr[" + std::to_string(i) + "]");
            }
            check_child(children, foo, vpiRefObj, foo + ".plain");
            if (children.size() != 5) {
                check_failed("vpi_iterate(vpiInternalScope, <" + foo + ">) yielded "
                             + std::to_string(children.size()) + " children, expected 5");
            }
        }
    }

    // The top yields its child scopes but no references, as it declares none
    {
        const TestVpiHandle toph = vpi_handle_by_name(const_cast<PLI_BYTE8*>(top.c_str()), NULL);
        if (!toph) {
            check_failed("vpi_handle_by_name('" + top + "') = NULL");
        } else {
            const auto children = children_of(toph, top);
            check_child(children, top, vpiModule, foo);
            for (int i = 0; i < 4; ++i) {
                check_child(children, top, vpiInterface,
                            top + ".top_arr[" + std::to_string(i) + "]");
            }
            check_child(children, top, vpiInterface, top + ".top_plain");
            for (const auto& child : children) {
                if (child.first == vpiRefObj) {
                    check_failed("vpi_iterate(vpiInternalScope, <" + top + ">) yielded reference '"
                                 + child.second + "'");
                }
            }
        }
    }

    // Each iterated reference has the element name, and resolves to its element
    {
        const TestVpiHandle fooh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(foo.c_str()), NULL);
        TestVpiHandle it = fooh ? vpi_iterate(vpiInternalScope, fooh) : NULL;
        if (it) {
            while (vpiHandle h = vpi_scan(it)) {
                const std::string fn = str_of(h, vpiFullName);
                const std::string::size_type dot = fn.rfind('.');
                check_str(h, vpiName, "'" + fn + "'", fn.substr(dot + 1));
                vpi_release_handle(h);
            }
            it.freed();
        }
    }
    for (int i = 0; i < 4; ++i) {
        check_actual(foo + ".arr[" + std::to_string(i) + "]", true,
                     top + ".top_arr[" + std::to_string(i) + "]");
    }
    check_actual(foo + ".plain", false, top + ".top_plain");

    // Nothing is named after the array itself; the tool builds that from the elements
    {
        const std::string arr = foo + ".arr";
        const TestVpiHandle arrh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(arr.c_str()), NULL);
        if (arrh) {
            check_failed("vpi_handle_by_name('" + arr + "') = " + str_of(arrh, vpiFullName)
                         + ", expected NULL");
        }
    }
}

#ifdef IS_VPI

static PLI_INT32 start_of_sim(t_cb_data* /*datap*/) {
    check_all();
    if (errors) {
        std::cout << "%Error: t_vpi_interface_ref_array.cpp: C Test failed with " << errors
                  << " error(s)" << std::endl;
        vpi_control(vpiStop);
    }
    return 0;
}

void vpi_compat_bootstrap(void) {
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

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

    {
        // Construct and destroy, so stale registrations would be visible below
        const std::unique_ptr<VM_PREFIX> topp{
            new VM_PREFIX{contextp.get(),
                          // Note null name - we're flattening it out
                          ""}};
    }

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

    check_all();
    if (errors) {
        std::cout << "%Error: t_vpi_interface_ref_array.cpp: C Test failed with " << errors
                  << " error(s)" << std::endl;
        return 10;
    }

    topp->eval();
    while (!contextp->gotFinish()) {
        contextp->timeInc(1);
        topp->eval();
        VerilatedVpi::callValueCbs();
    }
    topp->final();
    return 0;
}

#endif
