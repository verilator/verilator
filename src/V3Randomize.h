// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Node attributes/ expression widths
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3RANDOMIZE_METHOD_H_
#define VERILATOR_V3RANDOMIZE_METHOD_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3ThreadSafety.h"

class AstClass;
class AstFunc;
class AstNetlist;

class V3Randomize final {
public:
    static void randomizeNetlist(AstNetlist* nodep) VL_MT_DISABLED;

    static AstFunc* newRandomizeFunc(AstClass* nodep) VL_MT_DISABLED;
    static AstFunc* newSRandomFunc(AstClass* nodep) VL_MT_DISABLED;
};

#endif  // Guard
