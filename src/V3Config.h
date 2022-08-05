// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Configuration Files
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2010-2022 by Wilson Snyder. This program is free software; you
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

#include "V3Ast.h"
#include "V3Error.h"
#include "V3FileLine.h"

//######################################################################

class V3Config final {
public:
    static void addCaseFull(const string& file, int lineno);
    static void addCaseParallel(const string& file, int lineno);
    static void addCoverageBlockOff(const string& file, int lineno);
    static void addCoverageBlockOff(const string& module, const string& blockname);
    static void addIgnore(V3ErrorCode code, bool on, const string& filename, int min, int max);
    static void addInline(FileLine* fl, const string& module, const string& ftask, bool on);
    static void addModulePragma(const string& module, VPragmaType pragma);
    static void addProfileData(FileLine* fl, const string& model, const string& key,
                               uint64_t cost);
    static void addScopeTraceOn(bool on, const string& scope, int levels);
    static void addVarAttr(FileLine* fl, const string& module, const string& ftask,
                           const string& signal, VAttrType type, AstSenTree* nodep);
    static void addWaiver(V3ErrorCode code, const string& filename, const string& message);

    static void applyCase(AstCase* nodep);
    static void applyCoverageBlock(AstNodeModule* modulep, AstBegin* nodep);
    static void applyFTask(AstNodeModule* modulep, AstNodeFTask* ftaskp);
    static void applyIgnores(FileLine* filelinep);
    static void applyModule(AstNodeModule* modulep);
    static void applyVarAttr(AstNodeModule* modulep, AstNodeFTask* ftaskp, AstVar* varp);

    static uint64_t getProfileData(const string& model, const string& key);
    static FileLine* getProfileDataFileLine();
    static bool getScopeTraceOn(const string& scope);
    static bool waive(FileLine* filelinep, V3ErrorCode code, const string& message);
};

#endif  // Guard
