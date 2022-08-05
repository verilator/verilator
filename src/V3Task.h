// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inlining of modules
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

#ifndef VERILATOR_V3TASK_H_
#define VERILATOR_V3TASK_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"

#include <utility>
#include <vector>

//============================================================================

using V3TaskConnect = std::pair<AstVar*, AstArg*>;  // [port, pin-connects-to]
using V3TaskConnects = std::vector<V3TaskConnect>;  // [ [port, pin-connects-to] ... ]

//============================================================================

class V3Task final {
public:
    static void taskAll(AstNetlist* nodep);
    /// Return vector of [port, pin-connects-to]  (SLOW)
    static V3TaskConnects taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp);
    static string assignInternalToDpi(AstVar* portp, bool isPtr, const string& frSuffix,
                                      const string& toSuffix, const string& frPrefix = "");
    static string assignDpiToInternal(const string& lhsName, AstVar* rhsp);
    static const char* dpiTemporaryVarSuffix();
};

#endif  // Guard
