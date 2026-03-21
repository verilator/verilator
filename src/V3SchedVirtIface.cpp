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
// Each interface type written to via virtual interface, or written to normally but read via
// virtual interface:
//     Create a trigger var for it
// Each statement:
//     If it writes to a virtual interface, or to a variable read via virtual interface:
//         Set the corresponding trigger to 1
//         If the write is done by an AssignDly, the trigger is also set by AssignDly
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AstNodeExpr.h"
#include "V3Sched.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

class VirtIfaceVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVarRef::user1() -> bool. Whether it has been visited
    // AstMemberSel::user1() -> bool. Whether it has been visited
    const VNUser1InUse m_user1InUse;

    // TYPES
    using OnWriteToVirtIface = std::function<void(AstVarRef*, AstIface*)>;
    using OnWriteToVirtIfaceMember
        = std::function<void(AstVarRef*, AstIface*, const std::string&)>;

    // STATE
    AstNetlist* const m_netlistp;  // Root node
    V3UniqueNames m_vifTriggerNames{"__VvifTrigger"};  // Unique names for virt iface
                                                       // triggers
    VirtIfaceTriggers m_triggers;  // Interfaces and corresponding trigger vars

    // METHODS
    // For each write across a virtual interface boundary
    // Returns true if there is a write across a virtual interface boundary
    static bool writesToVirtIface(const AstNode* const nodep) {
        return nodep->exists([](const AstVarRef* const refp) {
            if (!refp->access().isWriteOrRW()) return false;
            AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType);
            const bool writesToVirtIfaceMember
                = (dtypep && dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel));
            const bool writesToIfaceSensVar = refp->varp()->isVirtIface();
            return writesToVirtIfaceMember || writesToIfaceSensVar;
        });
    }

    // Create trigger reference for a specific interface member
    AstVarRef* createVirtIfaceMemberTriggerRefp(FileLine* const flp, AstIface* ifacep,
                                                const AstVar* memberVarp) {
        // Check if we already have a trigger for this specific member
        AstVarScope* existingTrigger = m_triggers.findMemberTrigger(ifacep, memberVarp);
        if (!existingTrigger) {
            AstScope* const scopeTopp = m_netlistp->topScopep()->scopep();
            // Create a unique name for this member trigger
            const std::string triggerName
                = m_vifTriggerNames.get(ifacep) + "_Vtrigm_" + memberVarp->name();
            AstVarScope* const vscp = scopeTopp->createTemp(triggerName, 1);
            m_triggers.addMemberTrigger(ifacep, memberVarp, vscp);
            existingTrigger = vscp;
        }
        return new AstVarRef{flp, existingTrigger, VAccess::WRITE};
    }

    static void markIgnoreSchedRead(AstVarRef* nodep) { nodep->setIgnoreSchedRead(); }
    static void markIgnoreSchedRead(AstMemberSel*) {}

    template <typename T>
    void handleIface(T nodep) {
        static_assert(std::is_same<typename std::remove_cv<T>::type,
                                   typename std::add_pointer<AstVarRef>::type>::value
                          || std::is_same<typename std::remove_cv<T>::type,
                                          typename std::add_pointer<AstMemberSel>::type>::value,
                      "Node has to be of AstVarRef* or AstMemberSel* type");
        if (nodep->access().isReadOnly()) return;
        if (nodep->user1SetOnce()) return;
        AstIface* ifacep = nullptr;
        AstVar* memberVarp = nullptr;
        if (nodep->varp()->isVirtIface()) {
            if (AstMemberSel* const memberSelp = VN_CAST(nodep->firstAbovep(), MemberSel)) {
                ifacep = VN_AS(nodep->varp()->dtypep(), IfaceRefDType)->ifacep();
                memberVarp = memberSelp->varp();
            }
        } else if ((ifacep = nodep->varp()->sensIfacep())) {
            memberVarp = nodep->varp();
        }

        if (ifacep && memberVarp) {
            FileLine* const flp = nodep->fileline();

            // For continuous assigns (AstAssignW), make the trigger conditional
            // on the value actually changing. This prevents infinite convergence
            // loops when combinational logic repeatedly writes the same value
            // through a VIF boundary:  trigger = (current_val != newval)
            // Only continuous assigns can cause convergence loops; procedural
            // assigns are clocked and don't have this problem.
            // The scheduling dependency cycles that would normally arise from
            // reading the current value are avoided because:
            //  - VIF path: V3OrderGraphBuilder skips all MemberSel on VIFs
            //  - sensIfacep path: cloned read VarRef has ignoreSchedRead set,
            //    which is checked by all scheduling dependency graph builders
            AstNodeExpr* oldValReadp = nullptr;
            AstNodeExpr* newValExprp = nullptr;
            if (nodep->varp()->isVirtIface()) {
                // VIF path: AST is AssignW(MemberSel(VarRef(vif), member), rhs).
                // nodep is VarRef(vif), look up through MemberSel to the Assign.
                AstMemberSel* const memberSelp = VN_CAST(nodep->firstAbovep(), MemberSel);
                if (memberSelp) {
                    if (const AstNodeAssign* const assignp
                        = VN_CAST(memberSelp->backp(), NodeAssign)) {
                        if (VN_IS(assignp, AssignW) && assignp->lhsp() == memberSelp) {
                            AstMemberSel* const clonedSelp = memberSelp->cloneTree(false);
                            clonedSelp->access(VAccess::READ);
                            oldValReadp = clonedSelp;
                            newValExprp = assignp->rhsp()->cloneTree(false);
                        }
                    }
                }
            } else {
                // sensIfacep() path: nodep is a VarRef directly in the Assign.
                if (const AstNodeAssign* const assignp = VN_CAST(nodep->backp(), NodeAssign)) {
                    if (VN_IS(assignp, AssignW) && assignp->lhsp() == nodep) {
                        T const clonedNodep = nodep->cloneTree(false);
                        clonedNodep->access(VAccess::READ);
                        // Mark this read invisible to scheduling dependency graphs
                        // to avoid cycles (reading and writing same var in one block).
                        // sensIfacep() is only set on plain VarRefs, so T is AstVarRef* here.
                        markIgnoreSchedRead(clonedNodep);
                        oldValReadp = clonedNodep;
                        newValExprp = assignp->rhsp()->cloneTree(false);
                    }
                }
            }

            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);

            AstVarRef* const trigWriteRefp
                = createVirtIfaceMemberTriggerRefp(flp, ifacep, memberVarp);

            AstNodeStmt* triggerStmtp = nullptr;
            if (oldValReadp && newValExprp) {
                // Conditional trigger: trigger = (current_val != newval)
                AstNodeExpr* const changedExprp = new AstNeq{flp, oldValReadp, newValExprp};
                triggerStmtp = new AstAssign{flp, trigWriteRefp, changedExprp};
            } else {
                // Fall back to unconditional trigger
                triggerStmtp
                    = new AstAssign{flp, trigWriteRefp, new AstConst{flp, AstConst::BitTrue{}}};
            }

            relinker.relink(new AstExprStmt{flp, triggerStmtp, nodep});
        }
    }

    // VISITORS
    void visit(AstNodeProcedure* nodep) override {
        // Not sure if needed, but be paranoid to match previous behavior as didn't optimize
        // before ..
        if (VN_IS(nodep, AlwaysPost) && writesToVirtIface(nodep)) {
            nodep->foreach([](AstVarRef* refp) { refp->varScopep()->optimizeLifePost(false); });
        }
        iterateChildren(nodep);
    }
    void visit(AstMemberSel* const nodep) override { handleIface(nodep); }
    void visit(AstVarRef* const nodep) override { handleIface(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit VirtIfaceVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        iterate(nodep);
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
        // Dump afer destructor so VNDeleter runs
        V3Global::dumpCheckGlobalTree("sched_vif", 0, dumpTreeEitherLevel() >= 6);
    }
    return triggers;
}

}  //namespace V3Sched
