// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2011 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"
#include "vpi_user.h"

#include <cstdio>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestVpi.h"

int errors = 0;

//======================================================================

#define NEED_EXTERNS

#ifdef NEED_EXTERNS
extern "C" {
extern void dpii_check();
}
#endif

//======================================================================

void dpi_bad() {
    {
        int res = svGetTime(0, nullptr);
        TEST_CHECK_EQ(res, -1);
    }
    {
        int res = svGetTimeUnit(0, nullptr);
        TEST_CHECK_EQ(res, -1);
    }
    {
        int res = svGetTimePrecision(0, nullptr);
        TEST_CHECK_EQ(res, -1);
    }
}

void dpi_show(svScope obj) {
    const char* namep;
    if (obj) {
        namep = svGetNameFromScope(obj);
    } else {
        namep = "global";
    }

    svTimeVal t;  // aka s_vpi_time
    t.type = vpiSimTime;
    int gres = svGetTime(obj, &t);
    vpi_printf(const_cast<char*>("%s svGetTime = %d %d,%d\n"), namep, gres, (int)t.high,
               (int)t.low);

    // These will both print the precision, because the 0 asks for global scope
    int32_t u = 99;
    int ures = svGetTimeUnit(obj, &u);
    int32_t p = 99;
    int pres = svGetTimePrecision(obj, &p);
    vpi_printf(const_cast<char*>("%s svGetTimeUnit = %d %d"), namep, ures, u);
    vpi_printf(const_cast<char*>("  svGetTmePrecision = %d %d\n"), pres, p);
}

void vpi_show(vpiHandle obj) {
    const char* namep;
    if (obj) {
        namep = vpi_get_str(vpiFullName, obj);
    } else {
        namep = "global";
    }

    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(obj, &t);
    vpi_printf(const_cast<char*>("%s vpiSimTime = %d,%d"), namep, (int)t.high, (int)t.low);

    // Should be same value as vpiSimTime, just converted to real
    t.type = vpiScaledRealTime;
    vpi_get_time(obj, &t);
    vpi_printf(const_cast<char*>("  vpiScaledRealTime = %g\n"), t.real);

    // These will both print the precision, because the 0 asks for global scope
    int u = vpi_get(vpiTimeUnit, obj);
    int p = vpi_get(vpiTimePrecision, obj);
    vpi_printf(const_cast<char*>("%s vpiTimeUnit = %d"), namep, u);
    vpi_printf(const_cast<char*>("  vpiTimePrecision = %d\n"), p);
}

void dpii_check() {
    dpi_bad();
    dpi_show(0);
    vpi_show(0);

    svScope smod = svGetScopeFromName("top.t");
    if (!smod) {
        vpi_printf(const_cast<char*>("-- Cannot svGetScopeFromName\n"));
    } else {
        dpi_show(smod);
    }

    TestVpiHandle mod = vpi_handle_by_name((PLI_BYTE8*)"top.t", NULL);
    if (!mod) {
        vpi_printf(const_cast<char*>("-- Cannot vpi_find module\n"));
    } else {
        vpi_show(mod);
    }
}
