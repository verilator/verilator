// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include <stdio.h>
#include <stdarg.h>
#include <fstream>
#include <iomanip>
#include <memory>

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Broken.h"

//======================================================================
// Statics

vluint64_t AstNode::s_editCntGbl=0;
vluint64_t AstNode::s_editCntLast=0;

// To allow for fast clearing of all user pointers, we keep a "timestamp"
// along with each userp, and thus by bumping this count we can make it look
// as if we iterated across the entire tree to set all the userp's to null.
int AstNode::s_cloneCntGbl=0;
int AstNode::s_userCntGbl=0;
int AstNode::s_user2CntGbl=0;
int AstNode::s_user3CntGbl=0;
int AstNode::s_user4CntGbl=0;
int AstNode::s_user5CntGbl=0;

//######################################################################
// V3AstType

ostream& operator<<(ostream& os, AstType rhs);

//######################################################################
// Creators

void AstNode::init() {
    editCountInc();
    m_fileline = NULL;
    m_nextp = NULL;
    m_backp = NULL;
    m_headtailp = this;	// When made, we're a list of only a single element
    m_op1p = NULL;
    m_op2p = NULL;
    m_op3p = NULL;
    m_op4p = NULL;
    m_iterpp = NULL;
    m_clonep = NULL;
    m_cloneCnt = 0;
    // Attributes
    m_signed = false;
    m_width = 0;
    m_widthMin = 0;
    m_userp = NULL;
    m_userCnt = 0;
    m_user2p = NULL;
    m_user2Cnt = 0;
    m_user3p = NULL;
    m_user3Cnt = 0;
    m_user4p = NULL;
    m_user4Cnt = 0;
    m_user5p = NULL;
    m_user5Cnt = 0;
}

string AstNode::shortName() const {
    string pretty = name();
    string::size_type pos;
    while ((pos=pretty.find("__PVT__")) != string::npos) {
	pretty.replace(pos, 7, "");
    }
    return pretty;
}

string AstNode::dedotName(const string& namein) {
    string pretty = namein;
    string::size_type pos;
    while ((pos=pretty.find("__DOT__")) != string::npos) {
	pretty.replace(pos, 7, ".");
    }
    if (pretty.substr(0,4) == "TOP.") pretty.replace(0,4,"");
    return pretty;
}

string AstNode::prettyName(const string& namein) {
    string pretty = namein;
    string::size_type pos;
    while ((pos=pretty.find("__BRA__")) != string::npos) {
	pretty.replace(pos, 7, "[");
    }
    while ((pos=pretty.find("__KET__")) != string::npos) {
	pretty.replace(pos, 7, "]");
    }
    while ((pos=pretty.find("__PVT__")) != string::npos) {
	pretty.replace(pos, 7, "");
    }
    return AstNode::dedotName(pretty);
}

int AstNode::widthPow2() const {
    // I.e.  width 30 returns 32, width 32 returns 32.
    uint32_t width = this->width();
    for (int p2=30; p2>=0; p2--) {
	if (width > (1UL<<p2)) return (1UL<<(p2+1));
    }
    return 1;
}

//######################################################################
// Insertion

inline void AstNode::debugTreeChange(const char* prefix, int lineno, bool next) {
#ifdef VL_DEBUG
    // Called on all major tree changers.
    // Only for use for those really nasty bugs relating to internals
    // Note this may be null.
    //if (debug()) {
    //	cout<<"-treeChange: V3Ast.cpp:"<<lineno<<" Tree Change for "<<prefix<<endl;
    //	v3Global.rootp()->dumpTree(cout,"-treeChange: ");
    //	if (next||1) this->dumpTreeAndNext(cout, prefix);
    //	else this->dumpTree(cout, prefix);
    //	this->checkTree();
    //	v3Global.rootp()->checkTree();
    //}
#endif
}

AstNode* AstNode::addNext(AstNode* newp) {
    // Add to m_nextp, returns this
    UASSERT(newp,"Null item passed to addNext\n");
    this->debugTreeChange("-addNextThs: ", __LINE__, false);
    newp->debugTreeChange("-addNextNew: ", __LINE__, true);
    if (this == NULL) {
	return (newp);
    } else {
	// Find end of old list
	AstNode* oldtailp = this;
	if (oldtailp->m_nextp) {
	    if (oldtailp->m_headtailp) {
		oldtailp = oldtailp->m_headtailp;  // This=beginning of list, jump to end
		UASSERT(!oldtailp->m_nextp, "Node had next, but headtail says it shouldn't");
	    } else {
		// Though inefficent, we are occasionally passed a addNext in the middle of a list.
		while (oldtailp->m_nextp != NULL) oldtailp = oldtailp->m_nextp;
	    }
	}
	// Link it in
	oldtailp->m_nextp = newp;
	newp->m_backp = oldtailp;
	// New tail needs the head
	AstNode* newtailp = newp->m_headtailp;
	AstNode* headp = oldtailp->m_headtailp;
	oldtailp->m_headtailp = NULL; // May be written again as new head
	newp->m_headtailp = NULL; // May be written again as new tail
	newtailp->m_headtailp = headp;
	headp->m_headtailp = newtailp;
	newp->editCountInc();
	if (oldtailp->m_iterpp) *(oldtailp->m_iterpp) = newp;	// Iterate on new item
    }
    this->debugTreeChange("-addNextOut:", __LINE__, true);
    return this;
}

AstNode* AstNode::addNextNull(AstNode* newp) {
    if (!newp) return this;
    return addNext(newp);
}

void AstNode::addNextHere(AstNode* newp) {
    // Add to m_nextp on exact node passed, not at the end.
    //  This could be at head, tail, or both (single)
    //  New  could be head of single node, or list
    UASSERT(newp,"Null item passed to addNext");
    UASSERT(this,"Null base node");
    UASSERT(newp->backp()==NULL,"New node (back) already assigned?");
    this->debugTreeChange("-addHereThs: ", __LINE__, false);
    newp->debugTreeChange("-addHereNew: ", __LINE__, true);
    newp->editCountInc();

    AstNode* addlastp = newp->m_headtailp;	// Last node in list to be added
    UASSERT(!addlastp->m_nextp, "Headtailp tail isn't at the tail");

    // Forward links
    AstNode* oldnextp = this->m_nextp;
    this->m_nextp = newp;
    addlastp->m_nextp = oldnextp;	// Perhaps null if 'this' is not list

    // Backward links
    if (oldnextp) oldnextp->m_backp = addlastp;
    newp->m_backp = this;

    // Head/tail
    AstNode* oldheadtailp = this->m_headtailp;
    //    (!oldheadtailp) 		// this was&is middle of list
    //    (oldheadtailp==this && !oldnext)// this was head AND tail (one node long list)
    //    (oldheadtailp && oldnextp) 	// this was&is head of list of not just one node, not tail
    //    (oldheadtailp && !oldnextp)	// this was tail of list, might also be head of one-node list
    //
    newp->m_headtailp = NULL;  		// Not at head any longer
    addlastp->m_headtailp = NULL;	// Presume middle of list
    // newp might happen to be head/tail after all, if so will be set again below
    if (oldheadtailp) {	// else in middle of list, no change
	if (oldheadtailp==this) {  // this was one node
	    this->m_headtailp = addlastp;	  // Was head/tail, now a tail
	    addlastp->m_headtailp = oldheadtailp; // Tail needs to remember head (or NULL)
	} else if (!oldnextp) {   // this was tail
	    this->m_headtailp = NULL;	  // No longer a tail
	    oldheadtailp->m_headtailp = addlastp; // Head gets new tail
	    addlastp->m_headtailp = oldheadtailp; // Tail needs to remember head (or NULL)
	} // else is head, and we're inserting into the middle, so no other change
    }

    if (this->m_iterpp) *(this->m_iterpp) = newp;	// Iterate on new item
    this->debugTreeChange("-addHereOut: ", __LINE__, true);
}

void AstNode::setOp1p(AstNode* newp) {
    UASSERT(newp,"Null item passed to setOp1p\n");
    UDEBUGONLY(if (m_op1p) this->v3fatalSrc("Adding to non-empty, non-list op1"););
    UDEBUGONLY(if (newp->m_backp) newp->v3fatalSrc("Adding already linked node");); 
    UDEBUGONLY(if (newp->m_nextp) newp->v3fatalSrc("Adding list to non-list op1");); 
    this->debugTreeChange("-setOp1pThs: ", __LINE__, false);
    newp->debugTreeChange("-setOp1pNew: ", __LINE__, true);
    m_op1p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    this->debugTreeChange("-setOp1pOut: ", __LINE__, false);
}

void AstNode::setOp2p(AstNode* newp) {
    UASSERT(newp,"Null item passed to setOp2p\n");
    UDEBUGONLY(if (m_op2p) this->v3fatalSrc("Adding to non-empty, non-list op2"););
    UDEBUGONLY(if (newp->m_backp) newp->v3fatalSrc("Adding already linked node");); 
    UDEBUGONLY(if (newp->m_nextp) newp->v3fatalSrc("Adding list to non-list op2");); 
    this->debugTreeChange("-setOp2pThs: ", __LINE__, false);
    newp->debugTreeChange("-setOp2pNew: ", __LINE__, true);
    m_op2p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    this->debugTreeChange("-setOp2pOut: ", __LINE__, false);
}

void AstNode::setOp3p(AstNode* newp) {
    UASSERT(newp,"Null item passed to setOp3p\n");
    UDEBUGONLY(if (m_op3p) this->v3fatalSrc("Adding to non-empty, non-list op3"););
    UDEBUGONLY(if (newp->m_backp) newp->v3fatalSrc("Adding already linked node");); 
    UDEBUGONLY(if (newp->m_nextp) newp->v3fatalSrc("Adding list to non-list op3");); 
    this->debugTreeChange("-setOp3pThs: ", __LINE__, false);
    newp->debugTreeChange("-setOp3pNew: ", __LINE__, true);
    m_op3p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    this->debugTreeChange("-setOp3pOut: ", __LINE__, false);
}

void AstNode::setOp4p(AstNode* newp) {
    UASSERT(newp,"Null item passed to setOp4p\n");
    UDEBUGONLY(if (m_op4p) this->v3fatalSrc("Adding to non-empty, non-list op4"););
    UDEBUGONLY(if (newp->m_backp) newp->v3fatalSrc("Adding already linked node");); 
    UDEBUGONLY(if (newp->m_nextp) newp->v3fatalSrc("Adding list to non-list op4");); 
    this->debugTreeChange("-setOp4pThs: ", __LINE__, false);
    newp->debugTreeChange("-setOp4pNew: ", __LINE__, true);
    m_op4p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    this->debugTreeChange("-setOp4pOut: ", __LINE__, false);
}

void AstNode::addOp1p(AstNode* newp) {
    UASSERT(newp,"Null item passed to addOp1p\n");
    if (!m_op1p) { op1p(newp); }
    else { m_op1p->addNext(newp); }
}

void AstNode::addOp2p(AstNode* newp) {
    UASSERT(newp,"Null item passed to addOp2p\n");
    if (!m_op2p) { op2p(newp); }
    else { m_op2p->addNext(newp); }
}

void AstNode::addOp3p(AstNode* newp) {
    UASSERT(newp,"Null item passed to addOp3p\n");
    if (!m_op3p) { op3p(newp); }
    else { m_op3p->addNext(newp); }
}

void AstNode::addOp4p(AstNode* newp) {
    UASSERT(newp,"Null item passed to addOp4p\n");
    if (!m_op4p) { op4p(newp); }
    else { m_op4p->addNext(newp); }
}

void AstNode::replaceWith(AstNode* newp) {
    // Replace oldp with this
    // Unlike a unlink/relink, children are changed to point to the new node.
    AstNRelinker repHandle;
    this->unlinkFrBack(&repHandle);
    repHandle.relink(newp);
}

void AstNRelinker::dump(ostream& str) {
    str<<" BK="<<(uint32_t*)m_backp;
    str<<" ITER="<<(uint32_t*)m_iterpp;
    str<<" CHG="<<(m_chg==RELINK_NEXT?"[NEXT] ":"");
    str<<(m_chg==RELINK_OP1?"[OP1] ":"");
    str<<(m_chg==RELINK_OP2?"[OP2] ":"");
    str<<(m_chg==RELINK_OP3?"[OP3] ":"");
    str<<(m_chg==RELINK_OP4?"[OP4] ":"");
}

AstNode* AstNode::unlinkFrBackWithNext(AstNRelinker* linkerp) {
    this->debugTreeChange("-unlinkWNextThs: ", __LINE__, true);
    AstNode* oldp = this;
    UASSERT(oldp->m_backp,"Node has no back, already unlinked?\n");
    oldp->editCountInc();
    AstNode* backp = oldp->m_backp;
    if (linkerp) {
	linkerp->m_oldp = oldp;
	linkerp->m_backp  = backp;
	linkerp->m_iterpp = oldp->m_iterpp;
	if (backp->m_nextp == oldp) linkerp->m_chg = AstNRelinker::RELINK_NEXT;
	else if (backp->m_op1p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP1;
	else if (backp->m_op2p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP2;
	else if (backp->m_op3p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP3;
	else if (backp->m_op4p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP4;
	else oldp->v3fatalSrc("Unlink of node with back not pointing to it.");
    }
    if (backp->m_nextp== oldp) {
	backp->m_nextp= NULL;
	// Old list gets truncated
	// New list becomes a list upon itself
	// Most common case is unlinking a entire operand tree
	// (else we'd probably call unlinkFrBack without next)
	// We may be in the middle of a list; we have no way to find head or tail!
	AstNode* oldtailp = oldp;
	while (oldtailp->m_nextp) oldtailp=oldtailp->m_nextp;
	// Create new head/tail of old list
	AstNode* oldheadp = oldtailp->m_headtailp;
	oldheadp->m_headtailp = oldp->m_backp;
	oldheadp->m_headtailp->m_headtailp = oldheadp;
	// Create new head/tail of extracted list
	oldp->m_headtailp = oldtailp;
	oldp->m_headtailp->m_headtailp = oldp;
    }
    else if (backp->m_op1p == oldp) backp->m_op1p = NULL;
    else if (backp->m_op2p == oldp) backp->m_op2p = NULL;
    else if (backp->m_op3p == oldp) backp->m_op3p = NULL;
    else if (backp->m_op4p == oldp) backp->m_op4p = NULL;
    else this->v3fatalSrc("Unlink of node with back not pointing to it.");
    // Relink
    oldp->m_backp = NULL;
    // Iterator fixup
    if (oldp->m_iterpp) *(oldp->m_iterpp) = NULL;
    oldp->m_iterpp = NULL;
    oldp->debugTreeChange("-unlinkWNextOut: ", __LINE__, true);
    return oldp;
}

AstNode* AstNode::unlinkFrBack(AstNRelinker* linkerp) {
    this->debugTreeChange("-unlinkFrBkThs: ", __LINE__, true);
    AstNode* oldp = this;
    UASSERT(oldp->m_backp,"Node has no back, already unlinked?\n");
    oldp->editCountInc();
    AstNode* backp = oldp->m_backp;
    if (linkerp) {
	linkerp->m_oldp = oldp;
	linkerp->m_backp  = backp;
	linkerp->m_iterpp = oldp->m_iterpp;
	if (backp->m_nextp == oldp) linkerp->m_chg = AstNRelinker::RELINK_NEXT;
	else if (backp->m_op1p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP1;
	else if (backp->m_op2p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP2;
	else if (backp->m_op3p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP3;
	else if (backp->m_op4p == oldp) linkerp->m_chg = AstNRelinker::RELINK_OP4;
	else this->v3fatalSrc("Unlink of node with back not pointing to it.");
    }
    if (backp->m_nextp== oldp) {
	// This node gets removed from middle (or tail) of list
	// Not head, since then oldp wouldn't be a next of backp...
	backp->m_nextp= oldp->m_nextp;
	if (backp->m_nextp) backp->m_nextp->m_backp = backp;
	// If it was a tail, back becomes new tail
	if (oldp->m_headtailp) {
	    backp->m_headtailp = oldp->m_headtailp;
	    backp->m_headtailp->m_headtailp = backp;
	}
    }
    else {
	if (backp->m_op1p == oldp) backp->m_op1p = oldp->m_nextp;
	else if (backp->m_op2p == oldp) backp->m_op2p = oldp->m_nextp;
	else if (backp->m_op3p == oldp) backp->m_op3p = oldp->m_nextp;
	else if (backp->m_op4p == oldp) backp->m_op4p = oldp->m_nextp;
	else this->v3fatalSrc("Unlink of node with back not pointing to it.");
	if (oldp->m_nextp) {
	    AstNode* newheadp = oldp->m_nextp;
	    newheadp->m_backp = backp;
	    newheadp->m_headtailp = oldp->m_headtailp;
	    newheadp->m_headtailp->m_headtailp = newheadp;
	}
    }
    // Iterator fixup
    if (oldp->m_iterpp) *(oldp->m_iterpp) = oldp->m_nextp;
    // Relink
    oldp->m_nextp = NULL;
    oldp->m_backp = NULL;
    oldp->m_headtailp = this;
    oldp->m_iterpp = NULL;
    oldp->debugTreeChange("-unlinkFrBkOut: ", __LINE__, true);
    return oldp;
}

void AstNode::relink(AstNRelinker* linkerp) {
    if (debug()>8) {	UINFO(0," EDIT:      relink: "); dumpPtrs();    }
    AstNode* newp = this;
    UASSERT(linkerp && linkerp->m_backp, "Need non-empty linker\n");
    UASSERT(newp->backp()==NULL, "New node already linked?\n");
    newp->editCountInc();

    if (debug()>8) { linkerp->dump(cout); cout<<endl; }

    AstNode* backp = linkerp->m_backp;
    this->debugTreeChange("-relinkNew: ", __LINE__, true);
    backp->debugTreeChange("-relinkTre: ", __LINE__, true);

    switch (linkerp->m_chg) {
    case AstNRelinker::RELINK_NEXT: backp->addNextHere(newp); break;
    case AstNRelinker::RELINK_OP1: relinkOneLink(backp->m_op1p /*ref*/, newp); break;
    case AstNRelinker::RELINK_OP2: relinkOneLink(backp->m_op2p /*ref*/, newp); break;
    case AstNRelinker::RELINK_OP3: relinkOneLink(backp->m_op3p /*ref*/, newp); break;
    case AstNRelinker::RELINK_OP4: relinkOneLink(backp->m_op4p /*ref*/, newp); break;
    default:
	this->v3fatalSrc("Relink of node without any link to change.");
	break;
    }
    // Relink
    newp->m_backp = backp;
    linkerp->m_backp = NULL;
    // Iterator fixup
    if (linkerp->m_iterpp) {
	// If we're iterating over a next() link, we need to follow links off the
	// NEW node.  Thus we pass iteration information via a pointer in the node.
	// This adds a unfortunate 4 bytes to every AstNode, but is faster then passing
	// across every function.
	// If anyone has a cleaner way, I'd be grateful.
	*(linkerp->m_iterpp) = newp;
	newp->m_iterpp = linkerp->m_iterpp;
    }
    // Empty the linker so not used twice accidentally
    linkerp->m_backp = NULL;
    this->debugTreeChange("-relinkOut: ", __LINE__, true);
}

void AstNode::relinkOneLink(AstNode*& pointpr,  // Ref to pointer that gets set to newp
			    AstNode* newp) {
    if (pointpr) {
        // We know there will be at least two elements when we are done,
	//    (newp & the old list).
	// We *ALLOW* the new node to have its own next list.
	// Likewise there may be a old list.
	// Insert the whole old list following the new node's list.
	// Thus a unlink without next, followed by relink, gives the same list.
	AstNode* newlistlastp=newp->m_headtailp;
        if (newlistlastp->m_nextp && newlistlastp!=newp) newp->v3fatalSrc("Headtailp tail isn't at the tail");
	AstNode* oldlistlastp = pointpr->m_headtailp;
        if (oldlistlastp->m_nextp && oldlistlastp!=pointpr) newp->v3fatalSrc("Old headtailp tail isn't at the tail");
	// Next links
	newlistlastp->m_nextp = pointpr;
	pointpr->m_backp = newlistlastp;
	// Head/tail
	pointpr->m_headtailp = NULL;  // Old head
	newlistlastp->m_headtailp = NULL;  // Old tail
	newp->m_headtailp = oldlistlastp;  // Head points to tail
	oldlistlastp->m_headtailp = newp;  // Tail points to head
    }
    pointpr = newp;
}

//======================================================================
// Clone

AstNode* AstNode::cloneTreeIter() {
    if (!this) return NULL;
    AstNode* newp = this->clone();
    newp->op1p(this->m_op1p->cloneTreeIterList());
    newp->op2p(this->m_op2p->cloneTreeIterList());
    newp->op3p(this->m_op3p->cloneTreeIterList());
    newp->op4p(this->m_op4p->cloneTreeIterList());
    newp->m_iterpp = NULL;
    newp->clonep(this);		// Save pointers to/from both to simplify relinking.
    this->clonep(newp);		// Save pointers to/from both to simplify relinking.
    return newp;
}

AstNode* AstNode::cloneTreeIterList() {
    // Clone list of nodes, set m_headtailp
    if (!this) return NULL;
    AstNode* newheadp = NULL;
    AstNode* newtailp = NULL;
    for (AstNode* oldp = this; oldp; oldp=oldp->m_nextp) {
	AstNode* newp = oldp->cloneTreeIter();
	newp->m_headtailp = NULL;
	newp->m_backp = newtailp;
	if (newtailp) newtailp->m_nextp = newp;
	if (!newheadp) newheadp = newp;
	newtailp = newp;
    }
    newheadp->m_headtailp = newtailp;
    newtailp->m_headtailp = newheadp;
    return newheadp;
}

AstNode* AstNode::cloneTree(bool cloneNextLink) {
    if (!this) return NULL;
    this->debugTreeChange("-cloneThs: ", __LINE__, cloneNextLink);
    cloneClearTree();
    AstNode* newp;
    if (cloneNextLink && this->m_nextp) {
	newp = cloneTreeIterList();
    } else {
	newp = cloneTreeIter();
	newp->m_nextp = NULL;
	newp->m_headtailp = newp;
    }
    newp->m_backp = NULL;
    newp->cloneRelinkTree();
    newp->debugTreeChange("-cloneOut: ", __LINE__, true);
    return newp;
}

//======================================================================
// Delete

void AstNode::deleteNode() {
    if (!this) return;
    UASSERT(m_backp==NULL,"Delete called on node with backlink still set\n");
    editCountInc();
    // Change links of old node so we coredump if used
    this->m_nextp = (AstNode*)1;
    this->m_backp = (AstNode*)1;
    this->m_headtailp = (AstNode*)1;
    this->m_op1p = (AstNode*)1;
    this->m_op2p = (AstNode*)1;
    this->m_op3p = (AstNode*)1;
    this->m_op4p = (AstNode*)1;
#if !defined(VL_DEBUG) || defined(VL_LEAK_CHECKS)
    delete this;	// Leak massively, so each pointer is unique and we can debug easier
#endif
}

AstNode::~AstNode() {
}

void AstNode::deleteTreeIter() {
    if (!this) return;
    // MUST be depth first!
    this->m_op1p->deleteTreeIter();
    this->m_op2p->deleteTreeIter();
    this->m_op3p->deleteTreeIter();
    this->m_op4p->deleteTreeIter();
    this->m_nextp->deleteTreeIter();
    this->m_backp = NULL;
    deleteNode();
}

void AstNode::deleteTree() {
    // deleteTree always deletes the next link, because you must have called
    // unlinkFromBack or unlinkFromBackWithNext as appropriate before calling this.
    if (!this) return;
    UASSERT(m_backp==NULL,"Delete called on node with backlink still set\n");
    this->debugTreeChange("-delete: ", __LINE__, true);
    // MUST be depth first!
    deleteTreeIter();
}

//======================================================================
// Iterators

void AstNode::iterateChildren(AstNVisitor& v, AstNUser* vup) {
    if (!this) return;
    m_op1p->iterateAndNext(v, vup);
    m_op2p->iterateAndNext(v, vup);
    m_op3p->iterateAndNext(v, vup);
    m_op4p->iterateAndNext(v, vup);
}

void AstNode::iterateListBackwards(AstNVisitor& v, AstNUser* vup) {
    if (!this) return;
    AstNode* nodep=this;
    while (nodep->m_nextp) nodep=nodep->m_nextp;
    while (nodep) {
	// Edits not supported: nodep->m_iterpp = &nodep;
  	nodep->accept(v, vup);
	if (nodep->backp()->m_nextp == nodep) nodep=nodep->backp();
	else nodep = NULL;  // else: backp points up the tree.
    }
}

void AstNode::iterateChildrenBackwards(AstNVisitor& v, AstNUser* vup) {
    if (!this) return;
    this->op1p()->iterateListBackwards(v,vup);
    this->op2p()->iterateListBackwards(v,vup);
    this->op3p()->iterateListBackwards(v,vup);
    this->op4p()->iterateListBackwards(v,vup);
}

void AstNode::iterateAndNext(AstNVisitor& v, AstNUser* vup) {
    // IMPORTANT: If you replace a node that's the target of this iterator,
    // then the NEW node will be iterated on next, it isn't skipped!
    // if (!this) return;  // Part of for()
    for (AstNode* nodep=this; nodep;) {
	AstNode* niterp = nodep;
	niterp->m_iterpp = &niterp;
  	niterp->accept(v, vup);
	// accept may do a replaceNode and change niterp on us...
	if (!niterp) return;
	niterp->m_iterpp = NULL;
	if (niterp!=nodep) { // Edited it
	    nodep = niterp;
	} else {  // Same node, just loop
	    nodep = niterp->m_nextp;
	}
    }
}

void AstNode::iterateAndNextIgnoreEdit(AstNVisitor& v, AstNUser* vup) {
    // Keep following the current list even if edits change it
    if (!this) return;
    for (AstNode* nodep=this; nodep; ) {
	AstNode* nnextp = nodep->m_nextp;
  	nodep->accept(v, vup);
	nodep = nnextp;
    }
}

//======================================================================

void AstNode::cloneRelinkTree() {
    if (!this) return;
    this->cloneRelink();
    m_op1p->cloneRelinkTree();
    m_op2p->cloneRelinkTree();
    m_op3p->cloneRelinkTree();
    m_op4p->cloneRelinkTree();
    m_nextp->cloneRelinkTree();  // Tail recursion
}

//======================================================================
// Comparison

bool AstNode::sameTree(AstNode* node2p) {
    return sameTreeIter(node2p, true);
}

bool AstNode::sameTreeIter(AstNode* node2p, bool ignNext) {
    // Return true if the two trees are identical
    if (this==NULL && node2p==NULL) return true;
    if (this==NULL || node2p==NULL) return false;
    if (this->type() != node2p->type()
	|| this->width() != node2p->width()
	|| this->isSigned() != node2p->isSigned()
	|| !this->same(node2p)) {
	return false;
    }
    return (this->op1p()->sameTreeIter(node2p->op1p(),false)
	    && this->op2p()->sameTreeIter(node2p->op2p(),false)
	    && this->op3p()->sameTreeIter(node2p->op3p(),false)
	    && this->op4p()->sameTreeIter(node2p->op4p(),false)
	    && (ignNext || this->nextp()->sameTreeIter(node2p->nextp(),false))
	);
}

//======================================================================
// Static utilities

ostream& operator<<(ostream& os, V3Hash rhs) {
    return os<<hex<<setw(2)<<setfill('0')<<rhs.depth()
	     <<"_"<<setw(6)<<setfill('0')<<rhs.hshval();
}

V3Hash::V3Hash(const string& name) {
    uint32_t val = 0;
    for (const char* c=name.c_str(); *c; c++) {
	val = val*31 + *c;
    }
    setBoth(1,val);
}

//======================================================================
// Debugging

void AstNode::checkTreeIter(AstNode* backp) {
    if (backp != this->backp()) {
	this->v3fatalSrc("Back node inconsistent");
    }
    if (op1p()) op1p()->checkTreeIterList(this);
    if (op2p()) op2p()->checkTreeIterList(this);
    if (op3p()) op3p()->checkTreeIterList(this);
    if (op4p()) op4p()->checkTreeIterList(this);
}

void AstNode::checkTreeIterList(AstNode* backp) {
    // Check a (possible) list of nodes, this is always the head of the list
    if (!this) v3fatalSrc("Null nodep");
    AstNode* headp = this;
    AstNode* tailp = this;
    for (AstNode* nodep=headp; nodep; nodep=nodep->nextp()) {
	nodep->checkTreeIter(backp);
	if (headp!=this && nextp()) this->v3fatalSrc("Headtailp should be null in middle of lists");
	tailp=nodep;
	backp=nodep;
    }
    if (headp->m_headtailp != tailp) headp->v3fatalSrc("Tail in headtailp is inconsistent");
    if (tailp->m_headtailp != headp) tailp->v3fatalSrc("Head in headtailp is inconsistent");
}

void AstNode::checkTree() {
    if (!this) return;
    if (!debug()) return;
    if (this->backp()) {
	// Linked tree- check only the passed node
	this->checkTreeIter(this->backp());
    } else {
	this->checkTreeIterList(this->backp());
    }
}

void AstNode::dumpPtrs(ostream& os) {
    os<<"This="<<typeName()<<" "<<(void*)this;
    os<<" back="<<(void*)backp();
    if (nextp()) os<<" next="<<(void*)nextp();
    if (m_headtailp==this) os<<" headtail=this";
    else os<<" headtail="<<(void*)m_headtailp;
    if (op1p()) os<<" op1p="<<(void*)op1p();
    if (op2p()) os<<" op2p="<<(void*)op2p();
    if (op3p()) os<<" op3p="<<(void*)op3p();
    if (op4p()) os<<" op4p="<<(void*)op4p();
    if (userp()) os<<" user="<<(void*)userp();
    if (m_iterpp) {
	os<<" iterpp="<<(void*)m_iterpp;
	os<<"*="<<(void*)*m_iterpp;
    }
    os<<endl;
}

void AstNode::dumpTree(ostream& os, const string& indent, int maxDepth) {
    if (!this) return;
    os<<indent<<" "<<this<<endl;
    if (debug()>8) { os<<indent<<"     "; dumpPtrs(os); }
    if (maxDepth==1) {
	if (op1p()||op2p()||op3p()||op4p()) { os<<indent<<"1: ...(maxDepth)"<<endl; }
    } else {
	for (AstNode* nodep=op1p(); nodep; nodep=nodep->nextp()) { nodep->dumpTree(os,indent+"1:",maxDepth-1); }
	for (AstNode* nodep=op2p(); nodep; nodep=nodep->nextp()) { nodep->dumpTree(os,indent+"2:",maxDepth-1); }
	for (AstNode* nodep=op3p(); nodep; nodep=nodep->nextp()) { nodep->dumpTree(os,indent+"3:",maxDepth-1); }
	for (AstNode* nodep=op4p(); nodep; nodep=nodep->nextp()) { nodep->dumpTree(os,indent+"4:",maxDepth-1); }
    }
}

void AstNode::dumpTreeAndNext(ostream& os, const string& indent, int maxDepth) {
    if (!this) return;
    for (AstNode* nodep=this; nodep; nodep=nodep->nextp()) {
	nodep->dumpTree(os, indent, maxDepth);
    }
}

void AstNode::dumpTreeFile(const string& filename, bool append) {
    if (v3Global.opt.dumpTree()) {
	{   // Write log & close
	    const auto_ptr<ofstream> logsp (V3File::new_ofstream(filename, append));
	    if (logsp->fail()) v3fatalSrc("Can't write "<<filename);
	    *logsp<<"Tree Dump from <e"<<dec<<editCountLast()<<">";
	    *logsp<<" to <e"<<dec<<editCountGbl()<<">"<<endl;
	    if (editCountGbl()==editCountLast() && 1) {  // Off, as messes up tree diffing
		*logsp<<endl;
		*logsp<<"No changes since last dump!\n";
	    } else {
		dumpTree(*logsp);
	    }
	}
    }
    if (v3Global.opt.debugCheck() || v3Global.opt.dumpTree()) {
	// Error check
	checkTree();
	// Broken isn't part of check tree because it can munge iterp's
	// set by other steps if it is called in the middle of other operations
	if (AstNetlist* netp=this->castNetlist()) V3Broken::brokenAll(netp);
    }
    // Next dump can indicate start from here
    editCountSetLast();
}

void AstNode::v3errorEnd(ostringstream& str) {
    if (this && m_fileline) {
	ostringstream nsstr;
	nsstr<<str.str();
	if (debug()) {
	    nsstr<<endl;
	    nsstr<<"-node: "<<this<<endl;
	}
	m_fileline->v3errorEnd(nsstr);
    } else {
	V3Error::v3errorEnd(str);
    }
}

//######################################################################

void AstNVisitor::doDeletes() {
    for (vector<AstNode*>::iterator it = m_deleteps.begin(); it != m_deleteps.end(); ++it) {
	(*it)->deleteTree();
    }
    m_deleteps.clear();
}
