// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers necessary for scheduling across
//                         virtual interfaces
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
// V3SchedVirtIface's Transformations:
//
// Identify interface members written through virtual interface variables (VIF writes).
// For each such member, collect all VarScopes across all instantiations of that
// interface type. Each VarScope gets its own value-change trigger in the scheduler.
//
// Also disables lifetime optimization for variables in AlwaysPost blocks that
// write through virtual interfaces.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AstNodeExpr.h"
#include "V3Sched.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

class VirtIfaceVisitor final : public VNVisitor {
private:
    // STATE
    // Set of (iface, member) pairs written through VIF -- defines which members need triggers
    std::set<std::pair<const AstIface*, const std::string>> m_vifWrittenMembers;
    // All candidate VarScopes of interface members (keyed by interface type + member name)
    std::map<std::pair<const AstIface*, const std::string>, std::vector<AstVarScope*>>
        m_candidateVscps;
    VirtIfaceTriggers m_triggers;

    // METHODS
    // Returns true if statement writes across a virtual interface boundary
    static bool writesToVirtIface(const AstNode* const nodep) {
        return nodep->exists([](const AstVarRef* const refp) {
            if (!refp->access().isWriteOrRW()) return false;
            AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType);
            return dtypep && dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel);
        });
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
        // Detect writes through VIF handles: vif.member = expr
        // AST shape: AssignX(MemberSel(VarRef(vif), "member"), rhs)
        if (nodep->access().isWriteOrRW() && nodep->varp()->isVirtIface()) {
            if (AstMemberSel* const memberSelp = VN_CAST(nodep->firstAbovep(), MemberSel)) {
                const AstIface* const ifacep
                    = VN_AS(nodep->varp()->dtypep(), IfaceRefDType)->ifacep();
                m_vifWrittenMembers.emplace(ifacep, memberSelp->varp()->name());
            }
        }
    }
    void visit(AstVarScope* nodep) override {
        // Collect candidate VarScopes. sensIfacep() is set on interface members
        // accessed via any MemberSel (virtual or non-virtual).
        if (const AstIface* const ifacep = nodep->varp()->sensIfacep()) {
            m_candidateVscps[{ifacep, nodep->varp()->name()}].push_back(nodep);
        }
    }
    void visit(AstNodeProcedure* nodep) override {
        // Disable lifetime optimization for variables in AlwaysPost blocks
        // that write to virtual interface members, as VIF reads may observe them
        if (VN_IS(nodep, AlwaysPost) && writesToVirtIface(nodep)) {
            nodep->foreach([](AstVarRef* refp) { refp->varScopep()->optimizeLifePost(false); });
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // Build final trigger list by intersecting VIF writes with candidate VarScopes
    void buildTriggers() {
        for (const auto& written : m_vifWrittenMembers) {
            const auto it = m_candidateVscps.find(written);
            if (it == m_candidateVscps.end()) continue;
            for (AstVarScope* const vscp : it->second) {
                const AstIface* const ifacep = written.first;
                m_triggers.addTrigger(ifacep, vscp->varp(), vscp);
            }
        }
    }

public:
    // CONSTRUCTORS
    explicit VirtIfaceVisitor(AstNetlist* nodep) {
        iterate(nodep);
        buildTriggers();
    }
    ~VirtIfaceVisitor() override = default;

    // METHODS
    VirtIfaceTriggers take_triggers() { return std::move(m_triggers); }
};

}  //namespace

VirtIfaceTriggers makeVirtIfaceTriggers(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    VirtIfaceTriggers triggers{};
    if (v3Global.hasVirtIfaces()) {
        triggers = VirtIfaceVisitor{nodep}.take_triggers();
        // Dump after destructor so VNDeleter runs
        V3Global::dumpCheckGlobalTree("sched_vif", 0, dumpTreeEitherLevel() >= 6);
    }
    return triggers;
}

}  //namespace V3Sched
