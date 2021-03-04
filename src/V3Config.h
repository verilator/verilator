// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Configuration Files
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2010-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3CONFIG_H_
#define VERILATOR_V3CONFIG_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Ast.h"

//######################################################################

class V3Config final {
public:
    static void addCaseFull(const string& file, int lineno);
    static void addCaseParallel(const string& file, int lineno);
    static void addCoverageBlockOff(const string& file, int lineno);
    static void addCoverageBlockOff(const string& module, const string& blockname);
    static void addIgnore(V3ErrorCode code, bool on, const string& filename, int min, int max);
    static void addWaiver(V3ErrorCode code, const string& filename, const string& message);
    static void addModulePragma(const string& module, AstPragmaType pragma);
    static void addInline(FileLine* fl, const string& module, const string& ftask, bool on);
    static void addVarAttr(FileLine* fl, const string& module, const string& ftask,
                           const string& signal, AstAttrType type, AstSenTree* nodep);
    static void applyCase(AstCase* nodep);
    static void applyCoverageBlock(AstNodeModule* modulep, AstBegin* nodep);
    static void applyIgnores(FileLine* filelinep);
    static void applyModule(AstNodeModule* modulep);
    static void applyFTask(AstNodeModule* modulep, AstNodeFTask* ftaskp);
    static void applyVarAttr(AstNodeModule* modulep, AstNodeFTask* ftaskp, AstVar* varp);
    static bool waive(FileLine* filelinep, V3ErrorCode code, const string& message);
};

#endif  // Guard
