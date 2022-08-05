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

// These require the above. Comment prevents clang-format moving them
#include "TestVpi.h"

//======================================================================

#define NEED_EXTERNS

#ifdef NEED_EXTERNS
extern "C" {
extern void dpii_check();
}
#endif

//======================================================================

void show(vpiHandle obj) {
    const char* namep;
    if (obj) {
        namep = vpi_get_str(vpiName, obj);
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
    show(0);

    TestVpiHandle mod = vpi_handle_by_name((PLI_BYTE8*)"top.t", NULL);
    if (!mod) {
        vpi_printf(const_cast<char*>("-- Cannot vpi_find module\n"));
    } else {
        show(mod);
    }
}
