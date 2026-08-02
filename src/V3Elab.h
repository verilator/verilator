// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convergent elaboration of dependent semantic facts
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ELAB_H_
#define VERILATOR_V3ELAB_H_

#include "config_build.h"
#include "verilatedos.h"

#include <functional>
#include <memory>
#include <unordered_set>

class AstClass;
class AstNode;
class AstNetlist;
class AstPin;
class AstVar;

//============================================================================

class V3Elab final {
    class ProjectionState;

    std::unique_ptr<ProjectionState> m_projectionStatep;
    std::unordered_set<AstVar*> m_deferredParamVarps;
    bool m_collectingDeferredParams = false;

public:
    V3Elab();
    ~V3Elab();
    void elab(AstNetlist* nodep) VL_MT_DISABLED;
    void publishClassSpecialization(AstNode* nodep) VL_MT_DISABLED;
    void resolveDependentProjections(
        AstNode* nodep, const std::function<void(AstNode*, AstClass*)>& specialize) VL_MT_DISABLED;
    void convergeTypeProjections() VL_MT_DISABLED;
    void beginDeferredParams() VL_MT_DISABLED;
    void deferParam(AstVar* varp) VL_MT_DISABLED;
    bool deferParamIfDependent(AstVar* varp) VL_MT_DISABLED;
    void convergeDeferredParams(AstNetlist* nodep) VL_MT_DISABLED;
    static void substituteParams(AstNode* nodep, AstPin* pinsp) VL_MT_DISABLED;

    VL_UNCOPYABLE(V3Elab);
};

#endif  // Guard
