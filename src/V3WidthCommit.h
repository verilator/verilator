// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cleanup stage in V3Width
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
	newp->dtypeFrom(nodep);
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
// Now that all widthing is complete,
// Copy all width() to widthMin().  V3Const expects this

class WidthCommitVisitor : public AstNVisitor {
    // NODE STATE
    // AstVar::user1p		-> bool, processed
    AstUser1InUse	m_inuser1;

public:
    // METHODS
    static AstConst* newIfConstCommitSize (AstConst* nodep) {
	if (((nodep->dtypep()->width() != nodep->num().width())
	     || !nodep->num().sized())
	    && !nodep->num().isString()) {  // Need to force the number from unsized to sized
	    V3Number num (nodep->fileline(), nodep->dtypep()->width());
	    num.opAssign(nodep->num());
	    num.isSigned(nodep->isSigned());
	    AstConst* newp = new AstConst(nodep->fileline(), num);
	    newp->dtypeFrom(nodep);
	    return newp;
	} else {
	    return NULL;
	}
    }

private:
    // METHODS
    void editDType(AstNode* nodep) {
	// Edit dtypes for this node
	nodep->dtypep(editOneDType(nodep->dtypep()));
    }
    AstNodeDType* editOneDType(AstNodeDType* nodep) {
	// See if the dtype/refDType can be converted to a standard one
	// This reduces the number of dtypes in the system, and since
	// dtypep() figures into sameTree() results in better optimizations
	if (!nodep) return NULL;
	// Recurse to handle the data type, as may change the size etc of this type
	if (!nodep->user1()) nodep->accept(*this,NULL);
	// Look for duplicate
	if (AstBasicDType* bdtypep = nodep->castBasicDType()) {
	    AstBasicDType* newp = nodep->findInsertSameDType(bdtypep);
	    if (newp != bdtypep && debug()>=9) {
		UINFO(9,"dtype replacement "); nodep->dumpSmall(cout);
		cout<<"  ---->  "; newp->dumpSmall(cout); cout<<endl;
	    }
	    return newp;
	}
	return nodep;
    }
    // VISITORS
    virtual void visit(AstConst* nodep, AstNUser*) {
	if (!nodep->dtypep()) nodep->v3fatalSrc("No dtype");
	nodep->dtypep()->accept(*this);  // Do datatype first
	if (AstConst* newp = newIfConstCommitSize(nodep)) {
	    nodep->replaceWith(newp);
	    AstNode* oldp = nodep; nodep = newp;
	    //if (debug()>4) oldp->dumpTree(cout,"  fixConstSize_old: ");
	    //if (debug()>4) newp->dumpTree(cout,"              _new: ");
	    pushDeletep(oldp); oldp=NULL;
	}
	editDType(nodep);
    }
    virtual void visit(AstNodeDType* nodep, AstNUser*) {
	visitIterateNodeDType(nodep);
    }
    virtual void visit(AstNodeClassDType* nodep, AstNUser*) {
	visitIterateNodeDType(nodep);
	nodep->clearCache();
    }
    void visitIterateNodeDType(AstNodeDType* nodep) {
	// Rather than use dtypeChg which may make new nodes, we simply edit in place,
	// as we don't need to preserve any widthMin's, and every dtype with the same width
	// gets an identical edit.
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->widthMinFromWidth();
	// Too late to any unspecified sign to be anything but unsigned
	if (nodep->numeric().isNosign()) nodep->numeric(AstNumeric::UNSIGNED);
	nodep->iterateChildren(*this);
	nodep->virtRefDTypep(editOneDType(nodep->virtRefDTypep()));
    }
    virtual void visit(AstNodePreSel* nodep, AstNUser*) {
	// This check could go anywhere after V3Param
	nodep->v3fatalSrc("Presels should have been removed before this point");
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	editDType(nodep);
    }
public:
    // CONSTUCTORS
    WidthCommitVisitor(AstNetlist* nodep) {
	// Were changing widthMin's, so the table is now somewhat trashed
	nodep->typeTablep()->clearCache();
	nodep->accept(*this);
	// Don't want to repairCache, as all needed nodes have been added back in
	// a repair would prevent dead nodes from being detected
    }
    virtual ~WidthCommitVisitor() {}
};

//######################################################################

#endif // Guard
