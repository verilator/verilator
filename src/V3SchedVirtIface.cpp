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
    using IfaceCallable = std::pair<AstIface*, AstNode*>;
    std::vector<IfaceCallable> m_reachableIfaceCallables;
    std::set<IfaceCallable> m_seenIfaceCallables;

    // METHODS
    void addCandidateVscp(const AstIface* const ifacep, AstVarScope* const vscp) {
        std::vector<AstVarScope*>& vscps = m_candidateVscps[{ifacep, vscp->varp()->name()}];
        if (std::find(vscps.begin(), vscps.end(), vscp) == vscps.end()) vscps.push_back(vscp);
    }

    static bool isConcreteIfaceMemberRef(const AstVarRef* const refp) {
        return refp->access().isWriteOrRW() && !refp->varp()->isFuncLocal()
               && !refp->varp()->isTemp() && !refp->varp()->isEvent() && refp->varScopep()
               && VN_IS(refp->varScopep()->scopep()->modp(), Iface);
    }

    static const AstIfaceRefDType* virtualIfaceDTypep(const AstNodeExpr* const nodep) {
        if (!nodep || !nodep->dtypep()) return nullptr;
        const AstIfaceRefDType* const dtypep = VN_CAST(nodep->dtypep()->skipRefp(), IfaceRefDType);
        return dtypep && dtypep->isVirtual() ? dtypep : nullptr;
    }

    void addReachable(AstIface* const ifacep, AstNode* const callablep) {
        if (!callablep) return;
        const IfaceCallable pair{ifacep, callablep};
        if (m_seenIfaceCallables.insert(pair).second) m_reachableIfaceCallables.push_back(pair);
    }

    bool addVirtualIfaceCall(const AstNodeExpr* const fromp, AstNode* const callablep) {
        const AstIfaceRefDType* const dtypep = virtualIfaceDTypep(fromp);
        if (!dtypep) return false;
        addReachable(dtypep->ifacep(), callablep);
        return true;
    }

    static bool isOtherVirtualIfaceCall(const AstIface* const ifacep,
                                        const AstNodeExpr* const fromp) {
        const AstIfaceRefDType* const dtypep = virtualIfaceDTypep(fromp);
        return dtypep && dtypep->ifacep() != ifacep;
    }

    void collectVirtualIfaceCall(AstMethodCall* const nodep) {
        addVirtualIfaceCall(nodep->fromp(), nodep->taskp());
    }

    void collectVirtualIfaceCall(AstCMethodCall* const nodep) {
        addVirtualIfaceCall(nodep->fromp(), nodep->funcp());
    }

    void collectConcreteIfaceWrite(AstIface* const ifacep, AstVarRef* const refp) {
        if (!isConcreteIfaceMemberRef(refp)) return;
        refp->varp()->sensIfacep(ifacep);
        m_vifWrittenMembers.emplace(ifacep, refp->varp()->name());
        addCandidateVscp(ifacep, refp->varScopep());
    }

    void collectCallableWrites(AstIface* const ifacep, AstNode* const callablep) {
        callablep->foreach(
            [this, ifacep](AstVarRef* const refp) { collectConcreteIfaceWrite(ifacep, refp); });
        callablep->foreach([this, ifacep](AstNodeFTaskRef* const refp) {
            if (const AstMethodCall* const methodp = VN_CAST(refp, MethodCall)) {
                if (addVirtualIfaceCall(methodp->fromp(), methodp->taskp())) return;
            }
            addReachable(ifacep, refp->taskp());
        });
        callablep->foreach([this, ifacep](AstNodeCCall* const callp) {
            if (const AstCMethodCall* const methodp = VN_CAST(callp, CMethodCall)) {
                if (addVirtualIfaceCall(methodp->fromp(), methodp->funcp())) return;
            }
            addReachable(ifacep, callp->funcp());
        });
    }

    // Returns true if statement writes across a virtual interface boundary
    bool writesToVirtIface(const AstNode* const nodep) const {
        return nodep->exists([this](const AstNode* const childp) {
            if (const AstMemberSel* const memberSelp = VN_CAST(childp, MemberSel)) {
                if (!memberSelp->access().isWriteOrRW()) return false;
                return virtualIfaceDTypep(memberSelp->fromp()) != nullptr;
            }
            if (const AstMethodCall* const methodp = VN_CAST(childp, MethodCall)) {
                const AstIfaceRefDType* const dtypep = virtualIfaceDTypep(methodp->fromp());
                return dtypep && methodp->taskp()
                       && callableWritesIfaceMember(dtypep->ifacep(), methodp->taskp());
            }
            if (const AstCMethodCall* const methodp = VN_CAST(childp, CMethodCall)) {
                const AstIfaceRefDType* const dtypep = virtualIfaceDTypep(methodp->fromp());
                return dtypep && methodp->funcp()
                       && callableWritesIfaceMember(dtypep->ifacep(), methodp->funcp());
            }
            return false;
        });
    }

    bool callableWritesIfaceMember(const AstIface* const ifacep,
                                   const AstNode* const callablep) const {
        std::set<const AstNode*> seen;
        std::vector<const AstNode*> workps{callablep};
        while (!workps.empty()) {
            const AstNode* const curp = workps.back();
            workps.pop_back();
            if (!seen.insert(curp).second) continue;
            if (curp->exists(
                    [](const AstVarRef* const refp) { return isConcreteIfaceMemberRef(refp); })) {
                return true;
            }
            curp->foreach([&workps, ifacep](const AstNodeFTaskRef* const refp) {
                if (const AstMethodCall* const methodp = VN_CAST(refp, MethodCall)) {
                    if (isOtherVirtualIfaceCall(ifacep, methodp->fromp())) return;
                }
                if (const AstNodeFTask* const calledp = refp->taskp()) workps.push_back(calledp);
            });
            curp->foreach([&workps, ifacep](const AstNodeCCall* const callp) {
                if (const AstCMethodCall* const methodp = VN_CAST(callp, CMethodCall)) {
                    if (isOtherVirtualIfaceCall(ifacep, methodp->fromp())) return;
                }
                if (const AstCFunc* const calledp = callp->funcp()) workps.push_back(calledp);
            });
        }
        return false;
    }

    // VISITORS
    void visit(AstMemberSel* nodep) override {
        // Detect writes through VIF: the MemberSel's fromp resolves to a virtual interface type.
        // Handles both direct VIF access (vif.member) and class chain (obj.vif.member).
        if (nodep->access().isWriteOrRW()) {
            if (const AstIfaceRefDType* const dtypep = virtualIfaceDTypep(nodep->fromp())) {
                m_vifWrittenMembers.emplace(dtypep->ifacep(), nodep->varp()->name());
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstMethodCall* nodep) override {
        collectVirtualIfaceCall(nodep);
        iterateChildren(nodep);
    }
    void visit(AstCMethodCall* nodep) override {
        collectVirtualIfaceCall(nodep);
        iterateChildren(nodep);
    }
    void visit(AstVarScope* nodep) override {
        // Collect candidate VarScopes. sensIfacep() is set on interface members
        // accessed via any MemberSel (virtual or non-virtual).
        if (const AstIface* const ifacep = nodep->varp()->sensIfacep()) {
            if (!nodep->varp()->isFuncLocal() && !nodep->varp()->isTemp()) {
                addCandidateVscp(ifacep, nodep);
            }
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

    void collectReachableWrites() {
        for (size_t i = 0; i < m_reachableIfaceCallables.size(); ++i) {
            const IfaceCallable& pair = m_reachableIfaceCallables[i];
            collectCallableWrites(pair.first, pair.second);
        }
    }

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
        collectReachableWrites();
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
