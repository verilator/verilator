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

#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestVpi.h"

int errors = 0;

//======================================================================

// Walk a packed struct with many packed struct members, iterating the members of each one
extern "C" int mon_check(int nmembers) {
    TestVpiHandle bigh = vpi_handle_by_name(const_cast<PLI_BYTE8*>("t.big"), nullptr);
    TEST_CHECK_NZ(bigh);
    if (!bigh) return errors;
    TEST_CHECK_EQ(vpi_get(vpiPacked, bigh), 1);
    TestVpiHandle iter = vpi_iterate(vpiMember, bigh);
    TEST_CHECK_NZ(iter);
    if (!iter) return errors;
    int count = 0;
    while (TestVpiHandle memberh = vpi_scan(iter)) {
        ++count;
        TEST_CHECK_EQ(vpi_get(vpiType, memberh), vpiStructVar);
        TEST_CHECK_EQ(vpi_get(vpiPacked, memberh), 1);
        // Packed members are iterated MSB first, so 'a' then 'b'
        TestVpiHandle leafIter = vpi_iterate(vpiMember, memberh);
        TEST_CHECK_NZ(leafIter);
        if (!leafIter) continue;
        TestVpiHandle ah = vpi_scan(leafIter);
        TEST_CHECK_NZ(ah);
        if (ah) TEST_CHECK_CSTR(vpi_get_str(vpiName, ah), "a");
        TestVpiHandle bh = vpi_scan(leafIter);
        TEST_CHECK_NZ(bh);
        if (bh) TEST_CHECK_CSTR(vpi_get_str(vpiName, bh), "b");
        TEST_CHECK_Z(vpi_scan(leafIter));
        leafIter.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
    }
    iter.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
    TEST_CHECK_EQ(count, nmembers);
    return errors;
}
