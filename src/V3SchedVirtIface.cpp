// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create triggers necessary for scheduling across
//                         virtual interfaces
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
    // AstIface::user1() -> AstVarScope*. Trigger var for this interface
    // AstCFunc::user1() -> bool. Is visited
    // AstCFunc::user2() -> bool. Has timing control
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // TYPES
    using OnWriteToVirtIface = std::function<void(AstVarRef*, AstIface*)>;
    using OnWriteToVirtIfaceMember
        = std::function<void(AstVarRef*, AstIface*, const std::string&)>;

    // STATE
    AstNetlist* const m_netlistp;  // Root node
    AstAssign* m_trigAssignp = nullptr;  // Previous/current trigger assignment
    AstIface* m_trigAssignIfacep = nullptr;  // Interface type whose trigger is assigned
                                             // by m_trigAssignp
    AstVar* m_trigAssignMemberVarp = nullptr;  // Member pointer whose trigger is assigned
    V3UniqueNames m_vifTriggerNames{"__VvifTrigger"};  // Unique names for virt iface
                                                       // triggers
    VirtIfaceTriggers m_triggers;  // Interfaces and corresponding trigger vars
    AstNodeStmt* m_curStmt = nullptr;  // Current statement
    bool m_hasTimingControl = false;  // Whether current CFunc has timing control

    // METHODS
    // For each write across a virtual interface boundary
    static void foreachWrittenVirtIface(AstNode* const nodep, const OnWriteToVirtIface& onWrite) {
        nodep->foreach([&](AstVarRef* const refp) {
            if (refp->access().isReadOnly()) return;
            if (AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType)) {
                if (dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel)) {
                    onWrite(refp, dtypep->ifacep());
                }
            } else if (AstIface* const ifacep = refp->varp()->sensIfacep()) {
                onWrite(refp, ifacep);
            }
        });
    }
    // Returns true if there is a write across a virtual interface boundary
    static bool writesToVirtIface(const AstNode* const nodep) {
        return nodep->exists([](const AstVarRef* const refp) {
            if (!refp->access().isWriteOrRW()) return false;
            AstIfaceRefDType* const dtypep = VN_CAST(refp->varp()->dtypep(), IfaceRefDType);
            const bool writesToVirtIfaceMember
                = (dtypep && dtypep->isVirtual() && VN_IS(refp->firstAbovep(), MemberSel));
            const bool writesToIfaceSensVar = refp->varp()->sensIfacep();
            return writesToVirtIfaceMember || writesToIfaceSensVar;
        });
    }
    // Error on write across a virtual interface boundary
    static void unsupportedWriteToVirtIfaceMember(AstNode* nodep, const char* locationp) {
        if (!nodep) return;
        foreachWrittenVirtIfaceMember(
            nodep, [locationp](AstVarRef* const selp, AstIface*, AstVar* varp) {
                selp->v3warn(E_UNSUPPORTED,
                             "Unsupported: Write to virtual interface in " << locationp);
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

    // VISITORS
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_trigAssignp);
        m_trigAssignp = nullptr;
        VL_RESTORER(m_trigAssignIfacep);
        m_trigAssignIfacep = nullptr;
        VL_RESTORER(m_trigAssignMemberVarp);
        m_trigAssignMemberVarp = nullptr;
        // Not sure if needed, but be paranoid to match previous behavior as didn't optimize
        // before ..
        if (VN_IS(nodep, AlwaysPost) && writesToVirtIface(nodep)) {
            nodep->foreach([](AstVarRef* refp) { refp->varScopep()->optimizeLifePost(false); });
        }
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        if (nodep->user1SetOnce()) return;
        // By default set hasTiming to true - it may generate some false positives but it is better
        // than generating false negatives.
        // False positive may occur when there are are two funcs and they both call each other
        nodep->user2(v3Global.usesTiming());
        VL_RESTORER(m_trigAssignp);
        m_trigAssignp = nullptr;
        VL_RESTORER(m_trigAssignIfacep);
        m_trigAssignIfacep = nullptr;
        VL_RESTORER(m_trigAssignMemberVarp);
        m_trigAssignMemberVarp = nullptr;
        VL_RESTORER(m_hasTimingControl);
        m_hasTimingControl = false;
        iterateChildren(nodep);
        nodep->user2(m_hasTimingControl);
    }
    void visit(AstNodeCCall* nodep) override {
        iterate(nodep->funcp());
        if (nodep->funcp()->user2()) {
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberVarp = nullptr;
            m_hasTimingControl = true;
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeIf* nodep) override {
        unsupportedWriteToVirtIfaceMember(nodep->condp(), "if condition");
        iterateAndNextNull(nodep->condp());
        bool hasTimingControl;
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberVarp);
            VL_RESTORER(m_hasTimingControl);
            m_hasTimingControl = false;
            iterateAndNextNull(nodep->thensp());
            hasTimingControl = m_hasTimingControl;
        }
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberVarp);
            VL_RESTORER(m_hasTimingControl);
            m_hasTimingControl = false;
            iterateAndNextNull(nodep->elsesp());
            hasTimingControl |= m_hasTimingControl;
        }
        if (hasTimingControl) {
            // Clear the trigger assignment, as there could have been timing controls in either
            // branch
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberVarp = nullptr;
            m_hasTimingControl = true;
        }
    }
    void visit(AstLoop* nodep) override {
        UASSERT_OBJ(!nodep->contsp(), nodep, "'contsp' only used before LinkJump");
        iterateAndNextNull(nodep->contsp());
        bool hasTimingControl;
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberVarp);
            VL_RESTORER(m_hasTimingControl);
            m_hasTimingControl = false;
            iterateAndNextNull(nodep->stmtsp());
            hasTimingControl = m_hasTimingControl;
        }
        if (hasTimingControl) {
            // Clear the trigger assignment, as there could have been timing controls in the loop
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberVarp = nullptr;
            m_hasTimingControl = true;
        }
    }
    void visit(AstLoopTest* nodep) override {
        unsupportedWriteToVirtIfaceMember(nodep->condp(), "loop condition");
    }
    void visit(AstJumpBlock* nodep) override {
        {
            VL_RESTORER(m_trigAssignp);
            VL_RESTORER(m_trigAssignIfacep);
            VL_RESTORER(m_trigAssignMemberVarp);
            iterateChildren(nodep);
        }
        if (v3Global.usesTiming()) {
            // Clear the trigger assignment, as there could have been timing controls in the jump
            // block
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberVarp = nullptr;
        }
    }
    void visit(AstNodeStmt* nodep) override {
        if (v3Global.usesTiming() && nodep->isTimingControl()) {
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberVarp = nullptr;
            m_hasTimingControl = true;
        }
        VL_RESTORER(m_curStmt);
        m_curStmt = nodep;
        iterateChildren(nodep);
    }
    void visit(AstVarRef* const nodep) override {
        if (!m_curStmt) return;
        if (nodep->access().isReadOnly()) return;
        AstIface* ifacep = nullptr;
        AstVar* memberVarp = nullptr;
        if (AstIfaceRefDType* const dtypep = VN_CAST(nodep->varp()->dtypep(), IfaceRefDType)) {
            if (dtypep->isVirtual()) {
                if (AstMemberSel* const memberSelp = VN_CAST(nodep->firstAbovep(), MemberSel)) {
                    // Extract the member varp from the MemberSel node
                    memberVarp = memberSelp->varp();
                    ifacep = dtypep->ifacep();
                }
            }
        } else if ((ifacep = nodep->varp()->sensIfacep())) {
            memberVarp = nodep->varp();
        } else if (VN_IS(nodep->backp(), AssignW)) {
            memberVarp = nodep->varScopep()->varp();
            AstNode* backp = memberVarp;
            while ((backp = backp->backp())) {
                if ((ifacep = VN_CAST(backp, Iface))) break;
            }
        }

        FileLine* const flp = nodep->fileline();
        if (ifacep && memberVarp) {
            if (ifacep != m_trigAssignIfacep || memberVarp != m_trigAssignMemberVarp) {
                // Write to different interface member than before - need new trigger assignment
                m_trigAssignIfacep = ifacep;
                m_trigAssignMemberVarp = memberVarp;
                m_trigAssignp = nullptr;
            }
            if (!m_trigAssignp) {
                m_trigAssignp
                    = new AstAssign{flp, createVirtIfaceMemberTriggerRefp(flp, ifacep, memberVarp),
                                    new AstConst{flp, AstConst::BitTrue{}}};
                m_curStmt->addNextHere(m_trigAssignp);
            }
        }
    }
    void visit(AstNodeExpr* const nodep) override {
        if (v3Global.usesTiming() && nodep->isTimingControl()) {
            m_trigAssignp = nullptr;
            m_trigAssignIfacep = nullptr;
            m_trigAssignMemberVarp = nullptr;
            m_hasTimingControl = true;
        }
        iterateChildren(nodep);
    }
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
