// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add C++ casts across expression size changes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2020 by Wilson Snyder.  This program is free software; you can
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
// V3Cast's Transformations:
//
// Each module:
//      For each math operator, if above operator requires 32 bits,
//      and this isn't, cast to 32 bits.
//      Likewise for 64 bit operators.
//
// C++ rules:
//      Integral promotions allow conversion to larger int.  Unsigned is only
//      used if a int would not fit the value.
//
//      Bools converts to int, not unsigned.
//
//      Most operations return unsigned if either operand is unsigned.
//
//      Unsignedness can be lost on results of the below operations, as they
//      may need the sign bit for proper operation:
//              /, %, /=, %=, <, <=, >, or >=
//
//      Signed values are always sign extended on promotion or right shift,
//      even if assigning to a unsigned.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Cast.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>

//######################################################################
// Cast state, as a visitor of each AstNode

class CastVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //   AstNode::user()                // bool.  Indicates node is of known size
    AstUser1InUse       m_inuser1;

    // STATE

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void insertCast(AstNode* nodep, int needsize) {  // We'll insert ABOVE passed node
        UINFO(4,"  NeedCast "<<nodep<<endl);
        AstNRelinker relinkHandle;
        nodep->unlinkFrBack(&relinkHandle);
        //
        AstCCast* castp = new AstCCast(nodep->fileline(), nodep, needsize, nodep->widthMin());
        relinkHandle.relink(castp);
        //if (debug()>8) castp->dumpTree(cout, "-castins: ");
        //
        ensureLower32Cast(castp);
        nodep->user1(1);  // Now must be of known size
    }
    int castSize(AstNode* nodep) {
        if (nodep->isQuad()) return VL_QUADSIZE;
        else if (nodep->width() <= 8) return 8;
        else if (nodep->width() <= 16) return 16;
        else return VL_IDATASIZE;
    }
    void ensureCast(AstNode* nodep) {
        if (castSize(nodep->backp()) != castSize(nodep)
            || !nodep->user1()) {
            insertCast(nodep, castSize(nodep->backp()));
        }
    }
    void ensureLower32Cast(AstCCast* nodep) {
        // If we have uint64 = CAST(uint64(x)) then the upcasting
        // really needs to be CAST(uint64(CAST(uint32(x))).
        // Otherwise a (uint64)(a>b) would return wrong value, as
        // less than has nondeterministic signedness.
        if (nodep->isQuad() && !nodep->lhsp()->isQuad()
            && !VN_IS(nodep->lhsp(), CCast)) {
            insertCast(nodep->lhsp(), VL_IDATASIZE);
        }
    }

    // VISITORS
    virtual void visit(AstNodeUniop* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
    }
    virtual void visit(AstNodeBiop* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1()
                    | nodep->rhsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
    }
    virtual void visit(AstNodeTriop* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1()
                    | nodep->rhsp()->user1()
                    | nodep->thsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
        if (nodep->sizeMattersThs()) ensureCast(nodep->thsp());
    }
    virtual void visit(AstCCast* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        ensureLower32Cast(nodep);
        nodep->user1(1);
    }
    virtual void visit(AstNegate* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
        if (nodep->lhsp()->widthMin()==1) {
            // We want to avoid a GCC "converting of negative value" warning
            // from our expansion of
            //    out = {32{a<b}}  =>   out = - (a<b)
            insertCast(nodep->lhsp(), castSize(nodep));
        } else {
            ensureCast(nodep->lhsp());
        }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (!nodep->lvalue()
            && !VN_IS(nodep->backp(), CCast)
            && VN_IS(nodep->backp(), NodeMath)
            && !VN_IS(nodep->backp(), ArraySel)
            && nodep->backp()->width()
            && castSize(nodep) != castSize(nodep->varp())) {
            // Cast vars to IData first, else below has upper bits wrongly set
            //  CData x=3; out = (QData)(x<<30);
            insertCast(nodep, castSize(nodep));
        }
        nodep->user1(1);
    }
    virtual void visit(AstConst* nodep) VL_OVERRIDE {
        // Constants are of unknown size if smaller than 33 bits, because
        // we're too lazy to wrap every constant in the universe in
        // ((IData)#).
        nodep->user1(nodep->isQuad() || nodep->isWide());
    }

    // NOPs
    virtual void visit(AstVar* nodep) VL_OVERRIDE {}

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CastVisitor(AstNetlist* nodep) {
        iterate(nodep);
    }
    virtual ~CastVisitor() {}
};

//######################################################################
// Cast class functions

void V3Cast::castAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        CastVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("cast", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
