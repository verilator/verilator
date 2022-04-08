// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Link modules/signals together
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LINKLVALUE_H_
#define VERILATOR_V3LINKLVALUE_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;
class AstNode;

//============================================================================

class V3LinkLValue final {
public:
    static void linkLValue(AstNetlist* nodep);
    static void linkLValueSet(AstNode* nodep);
};

#endif  // Guard
