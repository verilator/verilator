// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Configuration Files
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2010-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3CONFIG_H_
#define _V3CONFIG_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Ast.h"

//######################################################################

class V3Config {
public:
    static void addCaseFull(const string& file, int lineno);
    static void addCaseParallel(const string& file, int lineno);
    static void addCoverageBlockOff(const string& file, int lineno);
    static void addCoverageBlockOff(const string& module, const string& blockname);
    static void addIgnore(V3ErrorCode code, bool on, const string& filename, int min, int max);
    static void addWaiver(V3ErrorCode code, const string& filename, const string& msg);
    static void addInline(FileLine* fl, const string& module, const string& ftask, bool on);
    static void addVarAttr(FileLine* fl, const string& module, const string& ftask,
                           const string& signal, AstAttrType type, AstSenTree* nodep);
    static void applyCase(AstCase* nodep);
    static void applyCoverageBlock(AstNodeModule* modulep, AstBegin* nodep);
    static void applyIgnores(FileLine* filelinep);
    static void applyModule(AstNodeModule* nodep);
    static void applyFTask(AstNodeModule* modulep, AstNodeFTask* ftaskp);
    static void applyVarAttr(AstNodeModule* modulep, AstNodeFTask* ftaskp, AstVar* varp);
    static bool waive(FileLine* filelinep, V3ErrorCode code, const string& match);
};

#endif  // Guard
