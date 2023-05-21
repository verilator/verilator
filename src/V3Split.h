// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into separate statements to reduce temps
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

#ifndef VERILATOR_V3SPLIT_H_
#define VERILATOR_V3SPLIT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3ThreadSafety.h"

class AstNetlist;

//============================================================================

class V3Split final {
public:
    static void splitReorderAll(AstNetlist* nodep) VL_MT_DISABLED;
    static void splitAlwaysAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
