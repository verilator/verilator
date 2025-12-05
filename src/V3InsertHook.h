// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator:
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3INSERTHOOK_H_
#define VERILATOR_V3INSERTHOOK_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//=========================================================================

class V3InsertHook final {
public:
    static void findTargets(AstNetlist* nodep) VL_MT_DISABLED;
    static void insertHooks(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
