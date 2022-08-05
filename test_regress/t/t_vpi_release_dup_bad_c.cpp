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
//#include "verilated.h"

#include "Vt_vpi_release_dup_bad__Dpi.h"

//======================================================================

void dpii_check() {
    vpiHandle mod;  // Not TestVpiHandle as testing double free
    // Verilated::scopesDump();
    mod = vpi_handle_by_name((PLI_BYTE8*)"top.t", NULL);
    if (!mod) vpi_printf(const_cast<char*>("-- Cannot vpi_find module\n"));
#ifdef VL_NO_LEGACY
    vpi_release_handle(mod);
    vpi_release_handle(mod);
#else
    vpi_free_object(mod);  // using vpi_free_object instead of vpi_release_handle for coverage
    vpi_free_object(mod);  // error: double free
#endif
}
