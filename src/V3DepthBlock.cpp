// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3DepthBlock's Transformations:
//
// Each module:
//      For each deep block, create cfunc including that block.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3DepthBlock.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"

#include <algorithm>
#include <cstdarg>

//######################################################################

class DepthBlockVisitor : public AstNVisitor {
private:
    // NODE STATE

    // STATE
    AstNodeModule*      m_modp;         // Current module
    AstCFunc*           m_funcp;        // Current function
    int                 m_depth;        // How deep in an expression
    int                 m_deepNum;      // How many functions made

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstCFunc* createDeepFunc(AstNode* nodep) {
        AstNRelinker relinkHandle;
        nodep->unlinkFrBack(&relinkHandle);
        // Create function
        string name = m_funcp->name()+"__deep"+cvtToStr(++m_deepNum);
        AstCFunc* funcp = new AstCFunc(nodep->fileline(), name, NULL);
        funcp->argTypes(EmitCBaseVisitor::symClassVar());
        funcp->symProlog(true);
        funcp->slow(m_funcp->slow());
        funcp->addStmtsp(nodep);
        m_modp->addStmtp(funcp);
        // Call it at the point where the body was removed from
        AstCCall* callp = new AstCCall(nodep->fileline(), funcp);
        callp->argTypes("vlSymsp");
        UINFO(6,"      New "<<callp<<endl);
        //
        relinkHandle.relink(callp);
        return funcp;
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) {
        UINFO(4," MOD   "<<nodep<<endl);
        m_modp = nodep;
        m_deepNum = 0;
        iterateChildren(nodep);
        m_modp = NULL;
    }
    virtual void visit(AstCFunc* nodep) {
        // We recurse into this.
        int lastDepth = m_depth;
        AstCFunc* lastFuncp = m_funcp;
        {
            m_depth = 0;
            m_funcp = nodep;
            iterateChildren(nodep);
        }
        m_depth = lastDepth;
        m_funcp = lastFuncp;
    }
    void visitStmt(AstNodeStmt* nodep) {
        m_depth++;
        if (m_depth > v3Global.opt.compLimitBlocks()
            && !VN_IS(nodep, CCall)) {  // Already done
            UINFO(4, "DeepBlocks "<<m_depth<<" "<<nodep<<endl);
            AstNode* backp = nodep->backp();  // Only for debug
            if (debug()>=9) backp->dumpTree(cout, "-   pre : ");
            AstCFunc* funcp = createDeepFunc(nodep);
            iterate(funcp);
            if (debug()>=9) backp->dumpTree(cout, "-   post: ");
            if (debug()>=9) funcp->dumpTree(cout, "-   func: ");
        } else {
            iterateChildren(nodep);
        }
        m_depth--;
    }
    virtual void visit(AstNodeStmt* nodep) {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
        } else {
            visitStmt(nodep);
        }
    }

    virtual void visit(AstNodeMath* nodep) {}  // Accelerate
    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep) {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit DepthBlockVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_funcp = NULL;
        m_depth = 0;
        m_deepNum = 0;
        //
        iterate(nodep);
    }
    virtual ~DepthBlockVisitor() {}
};

//######################################################################
// DepthBlock class functions

void V3DepthBlock::depthBlockAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        DepthBlockVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("deepblock", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
