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

// A custom main is required to destroy and reconstruct a model in one context.
// The array test separately exercises the generated main and VPI startup callbacks.
#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE

#include "TestCheck.h"
#include "TestVpi.h"

#include <memory>
#include <set>
#include <string>

int errors = 0;

static const std::set<std::string> refNames{
    "t.foo.arr[0]",  "t.foo.arr[1]",  "t.foo.arr[2]", "t.foo.arr[3]", "t.foo.arr[4]",
    "t.foo.arr[5]",  "t.foo.arr[6]",  "t.foo.arr[7]", "t.foo.arr[8]", "t.foo.arr[9]",
    "t.foo.arr[10]", "t.foo.arr[11]", "t.foo.plain"};

static void check_live() {
    const TestVpiHandle scope = vpi_handle_by_name(const_cast<PLI_BYTE8*>("t.foo"), nullptr);
    TEST_CHECK_NZ(scope);
    if (!scope) return;
    TestVpiHandle it = vpi_iterate(vpiInternalScope, scope);
    TEST_CHECK_NZ(it);
    if (!it) return;
    std::set<std::string> remaining = refNames;
    unsigned count = 0;
    while (TestVpiHandle ref = vpi_scan(it)) {
        ++count;
        TEST_CHECK_EQ(vpi_get(vpiType, ref), vpiRefObj);
        const char* const fullname = vpi_get_str(vpiFullName, ref);
        TEST_CHECK_NZ(fullname);
        if (!fullname) continue;
        const std::string name = fullname;
        const auto erased = remaining.erase(name);
        TEST_CHECK_EQ_LABEL(name, erased, 1);
        if (!erased) continue;

        const TestVpiHandle byName
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name.c_str()), nullptr);
        TEST_CHECK_NZ_LABEL(name, byName);
        if (!byName) continue;
        TEST_CHECK_EQ(vpi_get(vpiType, byName), vpiRefObj);
        const TestVpiHandle actual = vpi_handle(vpiActual, ref);
        const TestVpiHandle namedActual = vpi_handle(vpiActual, byName);
        TEST_CHECK_NZ(actual);
        TEST_CHECK_NZ(namedActual);
        if (!actual || !namedActual) continue;

        const bool plain = name == "t.foo.plain";
        const std::string expected
            = plain ? "t.top_plain" : "t.top_arr" + name.substr(name.find('[')) + ".SomeModport";
        TEST_CHECK_EQ(vpi_get(vpiType, actual), plain ? vpiInterface : vpiModport);
        const char* const actualName = vpi_get_str(vpiFullName, actual);
        TEST_CHECK_NZ(actualName);
        if (actualName) TEST_CHECK_EQ_LABEL(name, std::string{actualName}, expected);
        TEST_CHECK_EQ(vpi_get(vpiType, namedActual), plain ? vpiInterface : vpiModport);
        const char* const namedActualName = vpi_get_str(vpiFullName, namedActual);
        TEST_CHECK_NZ(namedActualName);
        if (namedActualName) TEST_CHECK_EQ_LABEL(name, std::string{namedActualName}, expected);
    }
    it.freed();
    TEST_CHECK_EQ(count, refNames.size());
    TEST_CHECK_EQ(remaining.size(), 0);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    for (int generation = 0; generation < 2; ++generation) {
        {
            const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};
            check_live();
        }
        // Check before reconstruction: reusing an address could hide a stale entry.
        for (const std::string& name : refNames) {
            TEST_CHECK_Z(contextp->ifaceRefFind(name.c_str()));
        }
    }
    if (errors) return 1;
    std::cout << "*-* All Finished *-*" << std::endl;
    return 0;
}
