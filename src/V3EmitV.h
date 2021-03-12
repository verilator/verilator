// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog code for module tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3EMITV_H_
#define VERILATOR_V3EMITV_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3EmitV final {
public:
    static void verilogForTree(AstNode* nodep, std::ostream& os = std::cout);
    static void verilogPrefixedTree(AstNode* nodep, std::ostream& os, const string& prefix,
                                    int flWidth, AstSenTree* domainp, bool user3mark);
    static void emitvFiles();
    static void debugEmitV(const string& stage);
};

#endif  // Guard
