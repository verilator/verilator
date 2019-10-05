// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Pre C-Emit stage changes
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3UNROLL_H_
#define _V3UNROLL_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================
/// Unroller with saved state, so caller can determine when pushDelete's are executed.

class UnrollVisitor;

class UnrollStateful {
    // MEMBERS
    UnrollVisitor* m_unrollerp;
    VL_UNCOPYABLE(UnrollStateful);
public:
    // CONSTRUCTORS
    UnrollStateful();
    ~UnrollStateful();
    // METHODS
    void unrollGen(AstNodeFor* nodep, const string& beginName);
    void unrollAll(AstNetlist* nodep);
};

//============================================================================

class V3Unroll {
public:
    static void unrollAll(AstNetlist* nodep);
};

#endif  // Guard
