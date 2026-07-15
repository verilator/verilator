// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Analyze and lower source $finish propagation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3FINISH_H_
#define VERILATOR_V3FINISH_H_

#include "config_build.h"
#include "verilatedos.h"

#include <unordered_set>

class AstNetlist;
class AstNode;
class AstNodeFTaskRef;
class FinishAnalysisVisitor;

//============================================================================

class V3FinishEffects final {
    friend class FinishAnalysisVisitor;

    std::unordered_set<const AstNodeFTaskRef*> m_callsp;  // Finish-capable call sites
    std::unordered_set<const AstNode*> m_sourceUnitsp;  // All source-unit boundaries
    std::unordered_set<const AstNode*> m_unitsp;  // Finish-capable source units

public:
    bool empty() const { return m_callsp.empty() && m_unitsp.empty(); }
    bool isSourceUnit(const AstNode* nodep) const { return m_sourceUnitsp.count(nodep); }
    bool mayFinish(const AstNode* nodep) const { return m_unitsp.count(nodep); }
    bool mayFinish(const AstNodeFTaskRef* nodep) const;
};

class V3Finish final {
public:
    static V3FinishEffects analyzeForCoverage(AstNetlist* nodep) VL_MT_DISABLED;
    static void analyze(AstNetlist* nodep) VL_MT_DISABLED;
    static void analyzeContainment(AstNetlist* nodep) VL_MT_DISABLED;
    static void lower(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
