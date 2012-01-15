// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cleanup stage in V3Width
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3WIDTHCOMMIT_H_
#define _V3WIDTHCOMMIT_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include "V3Ast.h"

#ifndef _V3WIDTH_CPP_
# error "V3WidthCommit for V3Width internal use only"
#endif

//######################################################################

/// Remove all $signed, $unsigned, we're done with them.

class WidthRemoveVisitor : public AstNVisitor {
private:
    // VISITORS
    virtual void visit(AstSigned* nodep, AstNUser*) {
	replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()); nodep=NULL;
    }
    virtual void visit(AstUnsigned* nodep, AstNUser*) {
	replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()); nodep=NULL;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    void replaceWithSignedVersion(AstNode* nodep, AstNode* newp) {
	UINFO(6," Replace "<<nodep<<" w/ "<<newp<<endl);
	nodep->replaceWith(newp);
	newp->widthSignedFrom(nodep);
	pushDeletep(nodep); nodep=NULL;
    }
public:
    // CONSTRUCTORS
    WidthRemoveVisitor() {}
    virtual ~WidthRemoveVisitor() {}
    AstNode* mainAcceptEdit(AstNode* nodep) {
	return nodep->acceptSubtreeReturnEdits(*this);
    }
};

//######################################################################

class WidthCommitVisitor : public AstNVisitor {
    // Now that all widthing is complete,
    // Copy all width() to widthMin().  V3Const expects this
private:
    // VISITORS
    virtual void visit(AstConst* nodep, AstNUser*) {
	nodep->width(nodep->width(),nodep->width());
	if ((nodep->width() != nodep->num().width()) || !nodep->num().sized()) {
	    V3Number num (nodep->fileline(), nodep->width());
	    num.opAssign(nodep->num());
	    num.isSigned(nodep->isSigned());
	    AstNode* newp = new AstConst(nodep->fileline(), num);
	    nodep->replaceWith(newp);
	    //if (debug()>4) nodep->dumpTree(cout,"  fixConstSize_old: ");
	    //if (debug()>4)  newp->dumpTree(cout,"              _new: ");
	    pushDeletep(nodep); nodep=NULL;
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->width(nodep->width(),nodep->width());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodePreSel* nodep, AstNUser*) {
	// This check could go anywhere after V3Param
	nodep->v3fatalSrc("Presels should have been removed before this point");
    }
public:
    // CONSTUCTORS
    WidthCommitVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~WidthCommitVisitor() {}
};

//######################################################################

#endif // Guard
