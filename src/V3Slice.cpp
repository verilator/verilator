// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
// Slice TRANSFORMATIONS:
//	Top-down traversal (SliceVisitor):
//	  NODEASSIGN
//	    ARRAYSEL
//	      Compare the dimensions to the Var to check for implicit slices.
//	      Using ->length() calculate the number of clones needed.
//	    VARREF
//	      Check the dimensions of the Var for an implicit slice.
//	      Replace with ArraySel nodes if needed.
//	    SEL, EXTEND
//	      We might be assigning a 1-D packed array to a 2-D packed array,
//	      this is unsupported.
//	    SliceCloneVisitor (called if this node is a slice):
//	      NODEASSIGN
//	        Clone and iterate the clone:
//		  ARRAYSEL
//		    Modify bitp() for the new value and set ->length(1)
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>

#include "V3Global.h"
#include "V3Slice.h"
#include "V3Ast.h"
#include <vector>

class SliceCloneVisitor : public AstNVisitor {
    // NODE STATE
    // Inputs:
    //  AstArraySel::user1p()	    -> AstVarRef. The VarRef that the final ArraySel points to
    //  AstNodeAssign::user2()	    -> int. The number of clones needed for this assign
    //  AstArraySel::user3()	    -> bool.  Error detected

    // STATE
    vector<vector<unsigned> >	m_selBits;	// Indexes of the ArraySel we are expanding
    int				m_vecIdx;	// Current vector index
    unsigned			m_depth;	// Number of ArraySel's from the VarRef
    AstVarRef*			m_refp;		// VarRef under this ArraySel

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstArraySel* nodep, AstNUser*) {
	if (!nodep->backp()->castArraySel()) {
	    // This is the top of an ArraySel, setup for iteration
	    m_refp = nodep->user1p()->castNode()->castVarRef();
	    m_vecIdx += 1;
	    if (m_vecIdx == (int)m_selBits.size()) {
		m_selBits.push_back(vector<unsigned>());
		AstVar* varp = m_refp->varp();
		pair<uint32_t,uint32_t> arrDim = varp->dtypep()->dimensions(false);
		uint32_t dimensions = arrDim.second;
		// for 3-dimensions we want m_selBits[m_vecIdx]=[0,0,0]
		for (uint32_t i = 0; i < dimensions; ++i) {
		    m_selBits[m_vecIdx].push_back(0);
		}
	    }
	}
	nodep->iterateChildren(*this);
	if (nodep->fromp()->castVarRef()) {
	    m_depth = 0;
	} else {
	    ++m_depth;
	}
	// Check if m_selBits has overflowed
	if (m_selBits[m_vecIdx][m_depth] >= nodep->length()) {
	    m_selBits[m_vecIdx][m_depth] = 0;
	    if (m_depth + 1 < m_selBits[m_vecIdx].size())
		m_selBits[m_vecIdx][m_depth+1] += 1;
	}
	// Reassign the bitp()
	if (nodep->length() > 1) {
	    if (AstConst* bitp = nodep->bitp()->castConst()) {
		unsigned idx = nodep->start() + m_selBits[m_vecIdx][m_depth];
		AstNode* constp = new AstConst(bitp->fileline(), V3Number(bitp->fileline(), bitp->castConst()->num().width(), idx));
		bitp->replaceWith(constp);
	    } else {
		nodep->v3error("Unsupported: Only constants supported in slices");
	    }
	}
	if (!nodep->backp()->castArraySel()) {
	    // Top ArraySel, increment m_selBits
	    m_selBits[m_vecIdx][0] += 1;
	}
	nodep->length(1);
    }

    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	if (nodep->user2() < 2) return; // Don't need clones
	m_selBits.clear();
	UINFO(4, "Cloning "<<nodep->user2()<<" times: "<<nodep<<endl);
	for (int i = 0; i < nodep->user2(); ++i) {
	    // Clone the node and iterate over the clone
	    m_vecIdx = -1;
	    AstNodeAssign* clonep = nodep->cloneTree(false)->castNodeAssign();
	    clonep->iterateChildren(*this);
	    nodep->addNextHere(clonep);
	}
	nodep->unlinkFrBack()->deleteTree(); nodep = NULL;
    }

    // Not all Uniop nodes should be cloned down to a single bit
    void cloneUniop(AstNodeUniop* nodep) {
	if (nodep->user2() < 2) return; // Don't need clones
	m_selBits.clear();
	UINFO(4, "Cloning "<<nodep->user2()<<" times: "<<nodep<<endl);

	AstNode* lhsp = NULL;
	AstNode* rhsp = NULL;
	for (int i = 0; i < nodep->user2(); ++i) {
	    // Clone the node and iterate over the clone
	    m_vecIdx = -1;
	    AstNodeUniop* clonep = nodep->cloneTree(false)->castNodeUniop();
	    clonep->iterateChildren(*this);
	    if (!lhsp) lhsp = clonep;
	    else rhsp = clonep;
	    if (lhsp && rhsp) {
		switch (nodep->type()) {
		case AstType::atREDOR:
		    lhsp = new AstOr(nodep->fileline(), lhsp, rhsp);
		    break;
		case AstType::atREDAND:
		    lhsp = new AstAnd(nodep->fileline(), lhsp, rhsp);
		    break;
		case AstType::atREDXOR:
		    lhsp = new AstXor(nodep->fileline(), lhsp, rhsp);
		    break;
		case AstType::atREDXNOR:
		    lhsp = new AstXnor(nodep->fileline(), lhsp, rhsp);
		    break;
		default:
		    nodep->v3fatalSrc("Unsupported: Unary operation on multiple packed dimensions");
		    break;
		}
		rhsp = NULL;
	    }
	}
	nodep->addNextHere(lhsp);
	nodep->unlinkFrBack()->deleteTree(); nodep = NULL;
    }
    virtual void visit(AstRedOr* nodep, AstNUser*) {
	cloneUniop(nodep);
    }
    virtual void visit(AstRedAnd* nodep, AstNUser*) {
	cloneUniop(nodep);
    }
    virtual void visit(AstRedXor* nodep, AstNUser*) {
	cloneUniop(nodep);
    }
    virtual void visit(AstRedXnor* nodep, AstNUser*) {
	cloneUniop(nodep);
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    SliceCloneVisitor(AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~SliceCloneVisitor() {}
};

//*************************************************************************

class SliceVisitor : public AstNVisitor {
    // NODE STATE
    // Cleared on netlist
    //  AstNodeAssign::user1()	    -> bool.  True if find is complete
    //  AstUniop::user1()	    -> bool.  True if find is complete
    //  AstArraySel::user1p()	    -> AstVarRef. The VarRef that the final ArraySel points to
    //  AstNode::user2()	    -> int. The number of clones needed for this node
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;

    // TYPEDEFS
    typedef pair<uint32_t, uint32_t> ArrayDimensions;	// Array Dimensions (packed, unpacked)

    // STATE
    AstNode*		m_assignp;	// Assignment we are under
    AstNodeVarRef*	m_lhsVarRefp;	// Var on the LHS
    bool		m_extend;	// We have found an extend node
    bool		m_assignError;	// True if the current assign already has an error

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    unsigned explicitDimensions(AstArraySel* nodep) {
	// Find out how many explicit dimensions are in a given ArraySel.
	unsigned dim = 0;
	AstNode* fromp = nodep;
	AstArraySel* selp;
	do {
	    selp = fromp->castArraySel();
	    if (!selp) {
		nodep->user1p(fromp->castVarRef());
		selp = NULL;
		break;
	    } else {
		fromp = selp->fromp();
		if (fromp) ++dim;
	    }
	} while (fromp && selp);
	if (!nodep->user1p()) nodep->v3fatalSrc("Couldn't find VarRef under the ArraySel");
	return dim;
    }

    int countClones(AstArraySel* nodep) {
	// Count how many clones we need to make from this ArraySel
	int clones = 1;
	AstNode* fromp = nodep;
	AstArraySel* selp;
	do {
	    selp = fromp->castArraySel();
	    fromp = (selp) ? selp->fromp() : NULL;
	    if (fromp && selp) clones *= selp->length();
	} while (fromp && selp);
	return clones;
    }

    AstArraySel* insertImplicit(AstNode* nodep, unsigned start, unsigned count) {
	// Insert any implicit slices as explicit slices (ArraySel nodes).
	// Return a new pointer to replace nodep() in the ArraySel.
	UINFO(9,"  insertImplicit (start="<<start<<",c="<<count<<") "<<nodep<<endl);
	AstVarRef* refp = nodep->user1p()->castNode()->castVarRef();
	if (!refp) nodep->v3fatalSrc("No VarRef in user1 of node "<<nodep);
	AstVar* varp = refp->varp();
	AstNode* topp = nodep;
	for (unsigned i = start; i < start + count; ++i) {
	    AstNodeDType* dtypep = varp->dtypep()->dtypeDimensionp(i-1);
	    AstUnpackArrayDType* adtypep = dtypep->castUnpackArrayDType();
	    if (!adtypep) nodep->v3fatalSrc("insertImplicit tried to expand an array without an ArrayDType");
	    vlsint32_t msb = adtypep->msb();
	    vlsint32_t lsb = adtypep->lsb();
	    if (lsb > msb) {
		// Below code assumes big bit endian; just works out if we swap
		int x = msb; msb = lsb; lsb = x;
	    }
	    UINFO(9,"    ArraySel-child: "<<topp<<endl);
	    AstArraySel* newp = new AstArraySel(nodep->fileline(), topp, new AstConst(nodep->fileline(),lsb));
	    if (!newp->dtypep()) {
		newp->v3fatalSrc("ArraySel dtyping failed when resolving slice");  // see ArraySel constructor
	    }
	    newp->user1p(refp);
	    newp->start(lsb);
	    newp->length(msb - lsb + 1);
	    topp = newp;
	}
	return topp->castArraySel();
    }

    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// The LHS/RHS of an Assign may be to a Var that is an array. In this
	// case we need to create a slice across the entire Var
	if (m_assignp && !nodep->backp()->castArraySel()) {
	    pair<uint32_t,uint32_t> arrDim = nodep->varp()->dtypep()->dimensions(false);
	    uint32_t dimensions = arrDim.second;  // unpacked only
	    if (dimensions > 0) {
		AstVarRef* clonep = nodep->cloneTree(false);
		clonep->user1p(nodep);
		AstNode* newp = insertImplicit(clonep, 1, dimensions);
		nodep->replaceWith(newp); nodep = NULL;
		newp->accept(*this);
	    }
	}
    }

    virtual void visit(AstExtend* nodep, AstNUser*) {
	m_extend = true;
	if (m_assignp && m_assignp->user2() > 1 && !m_assignError) {
	    m_assignp->v3error("Unsupported: Assignment between unpacked arrays of different dimensions");
	    m_assignError = true;
	}
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstConst* nodep, AstNUser*) {
	m_extend = true;
	if (m_assignp && m_assignp->user2() > 1 && !m_assignError) {
	    m_assignp->v3error("Unsupported: Assignment between a constant and an array slice");
	    m_assignError = true;
	}
    }

    virtual void visit(AstArraySel* nodep, AstNUser*) {
	if (!m_assignp) return;
	if (nodep->user3()) return;  // Prevent recursion on just created nodes
	unsigned dim = explicitDimensions(nodep);
	AstVarRef* refp = nodep->user1p()->castNode()->castVarRef();
	pair<uint32_t,uint32_t> arrDim = refp->varp()->dtypep()->dimensions(false);
	uint32_t implicit = (arrDim.second) - dim;
	if (implicit > 0) {
	    AstArraySel* newp = insertImplicit(nodep->cloneTree(false), dim+1, implicit);
	    nodep->replaceWith(newp); nodep = newp;
	    nodep->user3(true);
	}
	int clones = countClones(nodep);
	if (m_assignp->user2() > 0 && m_assignp->user2() != clones) {
	    m_assignp->v3error("Slices of arrays in assignments must have the same unpacked dimensions");
	} else if (!m_assignp->user2()) {
	    if (m_extend && clones > 1 && !m_assignError) {
		m_assignp->v3error("Unsupported: Assignment between unpacked arrays of different dimensions");
		m_assignError = true;
	    }
	    if (clones > 1 && !refp->lvalue() && refp->varp() == m_lhsVarRefp->varp()
		&& !m_assignp->castAssignDly() && !m_assignError) {
		// LHS Var != RHS Var for a non-delayed assignment
		m_assignp->v3error("Unsupported: Slices in a non-delayed assignment with the same Var on both sides");
		m_assignError = true;
	    }
	    m_assignp->user2(clones);
	}
    }

    virtual void visit(AstSel* nodep, AstNUser*) {
	m_extend = true;
	if (m_assignp && m_assignp->user2() > 1 && !m_assignError) {
	    m_assignp->v3error("Unsupported: Assignment between unpacked arrays of different dimensions");
	    m_assignError = true;
	}
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	// The conditional must be a single bit so only look at the expressions
	nodep->expr1p()->accept(*this);
	nodep->expr2p()->accept(*this);
    }

    // Return the first AstVarRef under the node
    AstVarRef* findVarRefRecurse(AstNode* nodep) {
	AstVarRef* refp = nodep->castVarRef();
	if (refp) return refp;
	if (nodep->op1p()) {
	    refp = findVarRefRecurse(nodep->op1p());
	    if (refp) return refp;
	}
	if (nodep->op2p()) {
	    refp = findVarRefRecurse(nodep->op2p());
	    if (refp) return refp;
	}
	if (nodep->op3p()) {
	    refp = findVarRefRecurse(nodep->op3p());
	    if (refp) return refp;
	}
	if (nodep->op4p()) {
	    refp = findVarRefRecurse(nodep->op4p());
	    if (refp) return refp;
	}
	if (nodep->nextp()) {
	    refp = findVarRefRecurse(nodep->nextp());
	    if (refp) return refp;
	}
	return NULL;
    }

    void findImplicit(AstNodeAssign* nodep) {
	if (m_assignp) nodep->v3fatalSrc("Found a NodeAssign under another NodeAssign");
	m_assignp = nodep;
	m_assignError = false;
	m_extend = false;
	nodep->user1(true);
	// Record the LHS Var so we can check if the Var on the RHS is the same
	m_lhsVarRefp = findVarRefRecurse(nodep->lhsp());
	if (!m_lhsVarRefp) nodep->v3fatalSrc("Couldn't find a VarRef on the LHSP of an Assign");
	// Iterate children looking for ArraySel nodes. From that we get the number of elements
	// in the array so we know how many times we need to clone this assignment.
	nodep->iterateChildren(*this);
	if (nodep->user2() > 1) SliceCloneVisitor scv(nodep);
	m_assignp = NULL;
    }

    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    // Cleanup initArrays
	    if (AstInitArray* initp = nodep->rhsp()->castInitArray()) {
		//if (debug()>=9) nodep->dumpTree(cout, "-InitArrayIn:  ");
		AstNode* newp = NULL;
		int index = 0;
		while (AstNode* subp=initp->initsp()) {
		    AstNode* lhsp = new AstArraySel(nodep->fileline(),
						    nodep->lhsp()->cloneTree(false),
						    index++);
		    // cppcheck-suppress nullPointer
		    newp = newp->addNext(nodep->cloneType(lhsp, subp->unlinkFrBack()));
		}
		//if (debug()>=9) newp->dumpTreeAndNext(cout, "-InitArrayOut: ");
		nodep->replaceWith(newp);
		pushDeletep(nodep); nodep=NULL;
		return;  // WIll iterate in a moment
	    }
	    // Hasn't been searched for implicit slices yet
	    findImplicit(nodep);
	}
    }

    void expandUniOp(AstNodeUniop* nodep) {
	nodep->user1(true);
	unsigned dim = 0;
	if (AstArraySel* selp = nodep->lhsp()->castArraySel()) {
	    // We have explicit dimensions, either packed or unpacked
	    dim = explicitDimensions(selp);
	}
	if (dim == 0 && !nodep->lhsp()->castVarRef()) {
	    // No ArraySel nor VarRef, not something we can expand
	    nodep->iterateChildren(*this);
	} else {
	    AstVarRef* refp = findVarRefRecurse(nodep->lhsp());
	    ArrayDimensions varDim = refp->varp()->dtypep()->dimensions(false);
	    if ((int)(dim - varDim.second) < 0) {
		// Unpacked dimensions are referenced first, make sure we have them all
		nodep->v3error("Unary operator used across unpacked dimensions");
	    } else if ((int)(dim - (varDim.second)) < 0) {
		// Implicit packed dimensions are allowed, make them explicit
		uint32_t newDim = (varDim.second) - dim;
		AstNode* clonep = nodep->lhsp()->cloneTree(false);
		clonep->user1p(refp);
		AstNode* newp = insertImplicit(clonep, dim+1, newDim);
		nodep->lhsp()->replaceWith(newp); refp = NULL;
		int clones = countClones(nodep->lhsp()->castArraySel());
		nodep->user2(clones);
		SliceCloneVisitor scv(nodep);
	    }
	}
    }
    virtual void visit(AstRedOr* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    expandUniOp(nodep);
	}
    }
    virtual void visit(AstRedAnd* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    expandUniOp(nodep);
	}
    }
    virtual void visit(AstRedXor* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    expandUniOp(nodep);
	}
    }
    virtual void visit(AstRedXnor* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    expandUniOp(nodep);
	}
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    SliceVisitor(AstNetlist* rootp) {
	m_assignp = NULL;
	m_lhsVarRefp = NULL;
	rootp->accept(*this);
    }
    virtual ~SliceVisitor() {}
};

//######################################################################
// Link class functions

void V3Slice::sliceAll(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    SliceVisitor visitor(rootp);
    V3Global::dumpCheckGlobalTree("slices.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
