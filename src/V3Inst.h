// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity inst domains
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3INST_H_
#define _V3INST_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3Inst {
public:
    static void instAll(AstNetlist* nodep);
    static void dearrayAll(AstNetlist* nodep);
    static AstAssignW* pinReconnectSimple(AstPin* pinp, AstCell* cellp,
                                          bool forTristate, bool alwaysCvt=false);
    static void checkOutputShort(AstPin* nodep);
};

#endif  // Guard
