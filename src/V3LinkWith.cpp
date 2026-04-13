// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// LinkResolve TRANSFORMATIONS:
//      Top-down traversal
//          With vars: Fixup LambdaRefs
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkWith.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Link state, as a visitor of each AstNode

class LinkWithVisitor final : public VNVisitor {
    // NODE STATE

    // STATE
    // Below state needs to be preserved between each module call.
    string m_randcIllegalWhy;  // Why randc illegal
    AstNode* m_randcIllegalp = nullptr;  // Node causing randc illegal
    AstNodeExpr* m_currentRandomizeSelectp = nullptr;  // fromp() of current `randomize()` call
    bool m_inRandomizeWith = false;  // If in randomize() with (and no other with afterwards)

    // VISITORS
    void visit(AstConstraint* nodep) override {
        // V3LinkDot moved the isExternDef into the class, the extern proto was
        // checked to exist, and now isn't needed
        nodep->isExternDef(false);
        if (nodep->isExternProto()) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstConstraintBefore* nodep) override {
        VL_RESTORER(m_randcIllegalWhy);
        VL_RESTORER(m_randcIllegalp);
        m_randcIllegalWhy = "'solve before' (IEEE 1800-2023 18.5.9)";
        m_randcIllegalp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstDist* nodep) override {
        VL_RESTORER(m_randcIllegalWhy);
        VL_RESTORER(m_randcIllegalp);
        m_randcIllegalWhy = "'constraint dist' (IEEE 1800-2023 18.5.3)";
        m_randcIllegalp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstConstraintExpr* nodep) override {
        VL_RESTORER(m_randcIllegalWhy);
        VL_RESTORER(m_randcIllegalp);
        if (nodep->isSoft()) {
            m_randcIllegalWhy = "'constraint soft' (IEEE 1800-2023 18.5.13.1)";
            m_randcIllegalp = nodep;
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeVarRef* nodep) override {
        if (nodep->varp()) {  // Else due to dead code, might not have var pointer
            if (nodep->varp()->isRandC() && m_randcIllegalp) {
                nodep->v3error("Randc variables not allowed in "
                               << m_randcIllegalWhy << '\n'
                               << nodep->warnContextPrimary() << '\n'
                               << m_randcIllegalp->warnOther()
                               << "... Location of restricting expression\n"
                               << m_randcIllegalp->warnContextSecondary());
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeFTaskRef* nodep) override {
        VL_RESTORER(m_currentRandomizeSelectp);
        if (nodep->taskp()) {
            if (AstSequence* const seqp = VN_CAST(nodep->taskp(), Sequence))
                seqp->isReferenced(true);
        }

        if (nodep->name() == "randomize") {
            if (const AstMethodCall* const methodcallp = VN_CAST(nodep, MethodCall)) {
                if (m_inRandomizeWith) {
                    nodep->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: randomize() nested in inline randomize() constraints");
                }
                m_currentRandomizeSelectp = methodcallp->fromp();
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstMemberSel* nodep) override {
        if (m_inRandomizeWith && nodep->fromp()->isSame(m_currentRandomizeSelectp)) {
            // Replace member selects to the element
            // on which the randomize() is called with LambdaArgRef
            // This allows V3Randomize to work properly when
            // constrained variables are referred using that object
            AstNodeExpr* const prevFromp = nodep->fromp();
            AstNodeExpr* const newp
                = new AstLambdaArgRef{prevFromp->fileline(), prevFromp->name(), false};
            prevFromp->replaceWith(newp);
            pushDeletep(prevFromp);
        }
        iterateChildren(nodep);
    }

    void visit(AstWith* nodep) override {
        VL_RESTORER(m_inRandomizeWith);
        if (const AstMethodCall* const methodCallp = VN_CAST(nodep->backp(), MethodCall)) {
            m_inRandomizeWith = methodCallp->name() == "randomize";
        } else {
            m_inRandomizeWith = false;
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkWithVisitor(AstNetlist* rootp) { iterate(rootp); }
    ~LinkWithVisitor() override = default;
};

//######################################################################
// V3LinkWith class functions

void V3LinkWith::linkWith(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": ");
    { const LinkWithVisitor visitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkwith", 0, dumpTreeEitherLevel() >= 6);
}
