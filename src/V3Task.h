// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inlining of modules
//
// Code available from: https://verilator.org
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

#ifndef _V3TASK_H_
#define _V3TASK_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

#include <vector>

//============================================================================

typedef std::pair<AstVar*,AstArg*> V3TaskConnect;  // [port, pin-connects-to]
typedef std::vector<V3TaskConnect> V3TaskConnects;  // [ [port, pin-connects-to] ... ]

//============================================================================

class V3Task {
public:
    static void taskAll(AstNetlist* nodep);
    /// Return vector of [port, pin-connects-to]  (SLOW)
    static V3TaskConnects taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp);
    static string assignInternalToDpi(AstVar* portp, bool isRtn, bool isPtr,
                                      const string& frSuffix, const string& toSuffix,
                                      const string& frPrefix="");
    static bool dpiToInternalFrStmt(AstVar* portp, const string& frName, bool cvt,
                                    string& frstmt);
};

#endif  // Guard
