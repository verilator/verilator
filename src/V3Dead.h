// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dead branch elimination
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

#ifndef VERILATOR_V3DEAD_H_
#define VERILATOR_V3DEAD_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Dead final {
public:
    // Modules, no vars/dtypes
    static void deadifyModules(AstNetlist* nodep);
    // Modules, Data types
    static void deadifyDTypes(AstNetlist* nodep);
    static void deadifyDTypesScoped(AstNetlist* nodep);
    // Everything that's possible
    static void deadifyAll(AstNetlist* nodep);
    static void deadifyAllScoped(AstNetlist* nodep);
};

#endif  // Guard
