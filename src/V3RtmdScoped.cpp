// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Finish the run time model descriptors (RTMD) after V3Scope
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
// V3RtmdScoped's Transformations:
//
// After V3Scope, walks the descriptor tree built by V3Rtmd from the root, to know the
// hierarchical path of each variable. Variables of instances not traced, or turned off by control
// directives, are no longer traced. The references of variables not traced are cleared, so they
// are described without a value. Constants (variables with a value, e.g. parameters) instead
// reference the constant pool entry of the value, so the constant needs no storage in the model.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3ConstPool.h"
#include "V3Control.h"
#include "V3Rtmd.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Post V3Scope Rtmd transformations

class RtmdScoped final : public VNVisitor {
    // STATE
    std::string m_path;  // Trace path of the level being visited
    const AstRtmdInstance* m_instancep = nullptr;  // Instance naming the level that follows it
    VDouble0 m_statDropped;  // Statistic tracking

    // VISITORS
    void visit(AstRtmdInstance* nodep) override {  //
        m_instancep = nodep;
    }
    void visit(AstRtmdHier* nodep) override {
        VL_RESTORER_COPY(m_path);
        // The ROOTIO level is not part of the path
        if (nodep->kind() != VRtmdHierKind::ROOTIO) {
            m_path += (m_instancep ? m_instancep->name() : nodep->name()) + ".";
        }
        m_instancep = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstRtmdVar* nodep) override {
        // Nothing to do if the value is not accessible
        AstVarRef* const refp = nodep->refp();
        if (!refp) return;
        // Not traced if its instance is not, or the control directives turn it off
        if (!nodep->vscp()->isTrace() || !V3Control::getScopeTraceOn(m_path + nodep->name())) {
            nodep->traced(false);
        }
        // If the value is not needed at runtime, drop the reference
        if (!nodep->needsRuntimeAccess()) {
            ++m_statDropped;
            VL_DO_DANGLING(pushDeletep(refp->unlinkFrBack()), refp);
            return;
        }
        // A constant (e.g. parameter) would otherwise need storage only for this reference, so
        // read the value from the constant pool instead
        AstNodeExpr* const valuep = VN_AS(nodep->varp()->valuep(), NodeExpr);
        if (valuep && valuep->isConstantTree()) {
            refp->replaceWith(V3ConstPool::find(valuep));
            VL_DO_DANGLING(pushDeletep(refp), refp);
        }
    }
    // Interface references and partitions hold no variables of this model
    void visit(AstNode*) override {}

    // CONSTRUCTORS
    explicit RtmdScoped(AstNetlist* netlistp) {
        AstTopScope* const topScopep = netlistp->topScopep();
        AstRtmdHier* const rootp = topScopep->rtmdp();
        UASSERT_OBJ(rootp, netlistp, "Top scope has no run time model descriptor");
        // The root level is not part of the path, so iterate its children
        iterateChildren(rootp);
    }
    ~RtmdScoped() override {
        V3Stats::addStat("Rtmd, dropped variables post scope", m_statDropped);
    }

public:
    static void apply(AstNetlist* netlistp) { RtmdScoped{netlistp}; }
};

void V3Rtmd::scopedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    RtmdScoped::apply(nodep);
    V3Global::dumpCheckGlobalTree("rtmdscoped", 0, dumpTreeEitherLevel() >= 3);
}
