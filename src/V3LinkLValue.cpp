// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: LValue module/signal name references
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// LinkLValue TRANSFORMATIONS:
//      Top-down traversal
//          Set lvalue() attributes on appropriate VARREFs.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3LinkLValue.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <map>

//######################################################################
// Link state, as a visitor of each AstNode

class LinkLValueVisitor final : public VNVisitor {
private:
    // NODE STATE

    // STATE
    bool m_setContinuously = false;  // Set that var has some continuous assignment
    VAccess m_setRefLvalue;  // Set VarRefs to lvalues for pin assignments
    AstNodeFTask* m_ftaskp = nullptr;  // Function or task we're inside

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITs
    // Result handing
    virtual void visit(AstNodeVarRef* nodep) override {
        // VarRef: LValue its reference
        if (m_setRefLvalue != VAccess::NOCHANGE) nodep->access(m_setRefLvalue);
        if (nodep->varp()) {
            if (nodep->access().isWriteOrRW() && m_setContinuously) {
                nodep->varp()->isContinuously(true);
            }
            if (nodep->access().isWriteOrRW() && !m_ftaskp && nodep->varp()->isReadOnly()) {
                nodep->v3warn(ASSIGNIN,
                              "Assigning to input/const variable: " << nodep->prettyNameQ());
            }
        }
        iterateChildren(nodep);
    }

    // Nodes that start propagating down lvalues
    virtual void visit(AstPin* nodep) override {
        if (nodep->modVarp() && nodep->modVarp()->isWritable()) {
            // When the varref's were created, we didn't know the I/O state
            // Now that we do, and it's from a output, we know it's a lvalue
            m_setRefLvalue = VAccess::WRITE;
            iterateChildren(nodep);
            m_setRefLvalue = VAccess::NOCHANGE;
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeAssign* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        VL_RESTORER(m_setContinuously);
        {
            m_setRefLvalue = VAccess::WRITE;
            m_setContinuously = VN_IS(nodep, AssignW) || VN_IS(nodep, AssignAlias);
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = VAccess::NOCHANGE;
            m_setContinuously = false;
            iterateAndNextNull(nodep->rhsp());
        }
    }
    virtual void visit(AstRelease* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        VL_RESTORER(m_setContinuously);
        {
            m_setRefLvalue = VAccess::WRITE;
            m_setContinuously = false;
            iterateAndNextNull(nodep->lhsp());
        }
    }
    virtual void visit(AstCastDynamic* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->fromp());
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->top());
        }
    }
    virtual void visit(AstFOpen* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->filenamep());
            iterateAndNextNull(nodep->modep());
        }
    }
    virtual void visit(AstFOpenMcd* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->filenamep());
        }
    }
    virtual void visit(AstFClose* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
        }
    }
    virtual void visit(AstFError* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
            iterateAndNextNull(nodep->strp());
        }
    }
    virtual void visit(AstFFlush* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
        }
    }
    virtual void visit(AstFGetC* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
        }
    }
    virtual void visit(AstFGetS* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
            iterateAndNextNull(nodep->strgp());
        }
    }
    virtual void visit(AstFRead* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->memp());
            iterateAndNextNull(nodep->filep());
        }
    }
    virtual void visit(AstFScanF* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
            iterateAndNextNull(nodep->exprsp());
        }
    }
    virtual void visit(AstFUngetC* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->filep());
        }
    }
    virtual void visit(AstSScanF* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->exprsp());
        }
    }
    virtual void visit(AstSysIgnore* nodep) override {
        // Can't know if lvalue or not; presume so as stricter
        VL_RESTORER(m_setRefLvalue);
        iterateChildren(nodep);
    }
    virtual void visit(AstRand* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            if (!nodep->urandom()) m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->seedp());
        }
    }
    virtual void visit(AstReadMem* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->memp());
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->filenamep());
            iterateAndNextNull(nodep->lsbp());
            iterateAndNextNull(nodep->msbp());
        }
    }
    virtual void visit(AstTestPlusArgs* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->searchp());
        }
    }
    virtual void visit(AstValuePlusArgs* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->searchp());
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->outp());
        }
    }
    virtual void visit(AstSFormat* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->fmtp());
        }
    }
    void prepost_visit(AstNodeTriop* nodep) {
        VL_RESTORER(m_setRefLvalue);
        {
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->lhsp());
            iterateAndNextNull(nodep->rhsp());
            m_setRefLvalue = VAccess::WRITE;
            iterateAndNextNull(nodep->thsp());
        }
    }
    virtual void visit(AstPreAdd* nodep) override { prepost_visit(nodep); }
    virtual void visit(AstPostAdd* nodep) override { prepost_visit(nodep); }
    virtual void visit(AstPreSub* nodep) override { prepost_visit(nodep); }
    virtual void visit(AstPostSub* nodep) override { prepost_visit(nodep); }

    // Nodes that change LValue state
    virtual void visit(AstSel* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {
            iterateAndNextNull(nodep->lhsp());
            // Only set lvalues on the from
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->rhsp());
            iterateAndNextNull(nodep->thsp());
        }
    }
    virtual void visit(AstNodeSel* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {  // Only set lvalues on the from
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->rhsp());
        }
    }
    virtual void visit(AstCellArrayRef* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {  // selp is not an lvalue
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->selp());
        }
    }
    virtual void visit(AstNodePreSel* nodep) override {
        VL_RESTORER(m_setRefLvalue);
        {  // Only set lvalues on the from
            iterateAndNextNull(nodep->fromp());
            m_setRefLvalue = VAccess::NOCHANGE;
            iterateAndNextNull(nodep->rhsp());
            iterateAndNextNull(nodep->thsp());
        }
    }
    virtual void visit(AstNodeFTask* nodep) override {
        m_ftaskp = nodep;
        iterateChildren(nodep);
        m_ftaskp = nullptr;
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        AstNode* pinp = nodep->pinsp();
        const AstNodeFTask* const taskp = nodep->taskp();
        // We'll deal with mismatching pins later
        if (!taskp) return;
        for (AstNode* stmtp = taskp->stmtsp(); stmtp && pinp; stmtp = stmtp->nextp()) {
            if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO()) {
                    if (portp->isWritable()) {
                        m_setRefLvalue = VAccess::WRITE;
                        iterate(pinp);
                        m_setRefLvalue = VAccess::NOCHANGE;
                    } else {
                        iterate(pinp);
                    }
                    // Advance pin
                    pinp = pinp->nextp();
                }
            }
        }
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LinkLValueVisitor(AstNode* nodep, VAccess start)
        : m_setRefLvalue{start} {
        iterate(nodep);
    }
    virtual ~LinkLValueVisitor() override = default;
};

//######################################################################
// Link class functions

void V3LinkLValue::linkLValue(AstNetlist* nodep) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    { LinkLValueVisitor{nodep, VAccess::NOCHANGE}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linklvalue", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
void V3LinkLValue::linkLValueSet(AstNode* nodep) {
    // Called by later link functions when it is known a node needs
    // to be converted to a lvalue.
    UINFO(9, __FUNCTION__ << ": " << endl);
    { LinkLValueVisitor{nodep, VAccess::WRITE}; }
}
