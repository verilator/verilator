// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: LValue module/signal name references
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
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

#include "V3Global.h"
#include "V3LinkLValue.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <map>
#include <vector>

//######################################################################
// Link state, as a visitor of each AstNode

class LinkLValueVisitor : public AstNVisitor {
private:
    // NODE STATE

    // STATE
    bool        m_setRefLvalue;  // Set VarRefs to lvalues for pin assignments
    AstNodeFTask* m_ftaskp;      // Function or task we're inside

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITs
    // Result handing
    virtual void visit(AstNodeVarRef* nodep) VL_OVERRIDE {
        // VarRef: LValue its reference
        if (m_setRefLvalue) {
            nodep->lvalue(true);
        }
        if (nodep->varp()) {
            if (nodep->lvalue() && !m_ftaskp
                && nodep->varp()->isReadOnly()) {
                nodep->v3warn(ASSIGNIN, "Assigning to input/const variable: "
                              <<nodep->prettyNameQ());
            }
        }
        iterateChildren(nodep);
    }

    // Nodes that start propagating down lvalues
    virtual void visit(AstPin* nodep) VL_OVERRIDE {
        if (nodep->modVarp() && nodep->modVarp()->isWritable()) {
            // When the varref's were created, we didn't know the I/O state
            // Now that we do, and it's from a output, we know it's a lvalue
            m_setRefLvalue = true;
            iterateChildren(nodep);
            m_setRefLvalue = false;
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->rhsp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFOpen* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->filenamep());
            iterateAndNextNull(nodep->modep());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFClose* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFFlush* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFGetC* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFGetS* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
            iterateAndNextNull(nodep->strgp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFRead* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->memp());
            iterateAndNextNull(nodep->filep());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFScanF* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
            iterateAndNextNull(nodep->exprsp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFUngetC* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->filep());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstSScanF* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->exprsp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstSysIgnore* nodep) VL_OVERRIDE {
        // Can't know if lvalue or not; presume so as stricter
        bool last_setRefLvalue = m_setRefLvalue;
        iterateChildren(nodep);
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstReadMem* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->memp());
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->filenamep());
            iterateAndNextNull(nodep->lsbp());
            iterateAndNextNull(nodep->msbp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstValuePlusArgs* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->searchp());
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->outp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstSFormat* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            m_setRefLvalue = true;
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->fmtp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }

    // Nodes that change LValue state
    virtual void visit(AstSel* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {
            iterateAndNextNull(nodep->lhsp());
            // Only set lvalues on the from
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->rhsp());
            iterateAndNextNull(nodep->thsp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstNodeSel* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {   // Only set lvalues on the from
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->rhsp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstCellArrayRef* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {   // selp is not an lvalue
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->selp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstNodePreSel* nodep) VL_OVERRIDE {
        bool last_setRefLvalue = m_setRefLvalue;
        {   // Only set lvalues on the from
            iterateAndNextNull(nodep->lhsp());
            m_setRefLvalue = false;
            iterateAndNextNull(nodep->rhsp());
            iterateAndNextNull(nodep->thsp());
        }
        m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        m_ftaskp = nodep;
        iterateChildren(nodep);
        m_ftaskp = NULL;
    }
    virtual void visit(AstNodeFTaskRef* nodep) VL_OVERRIDE {
        AstNode* pinp = nodep->pinsp();
        AstNodeFTask* taskp = nodep->taskp();
        // We'll deal with mismatching pins later
        if (!taskp) return;
        for (AstNode* stmtp = taskp->stmtsp(); stmtp && pinp; stmtp=stmtp->nextp()) {
            if (const AstVar* portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO()) {
                    if (portp->isWritable()) {
                        m_setRefLvalue = true;
                        iterate(pinp);
                        m_setRefLvalue = false;
                    } else {
                        iterate(pinp);
                    }
                    // Advance pin
                    pinp = pinp->nextp();
                }
            }
        }
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // Default: Just iterate
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    LinkLValueVisitor(AstNode* nodep, bool start) {
        m_setRefLvalue = start;
        m_ftaskp = NULL;
        iterate(nodep);
    }
    virtual ~LinkLValueVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkLValue::linkLValue(AstNetlist* nodep) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    {
        LinkLValueVisitor visitor(nodep, false);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linklvalue", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
void V3LinkLValue::linkLValueSet(AstNode* nodep) {
    // Called by later link functions when it is known a node needs
    // to be converted to a lvalue.
    UINFO(9,__FUNCTION__<<": "<<endl);
    LinkLValueVisitor visitor(nodep, true);
}
