// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
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

#include <cstdio>
#include <cstdarg>
#include <fstream>
#include <iomanip>
#include <memory>

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Broken.h"

//======================================================================
// Statics

vluint64_t AstNode::s_editCntLast=0;
vluint64_t AstNode::s_editCntGbl=0;	// Hot cache line

// To allow for fast clearing of all user pointers, we keep a "timestamp"
// along with each userp, and thus by bumping this count we can make it look
// as if we iterated across the entire tree to set all the userp's to null.
int AstNode::s_cloneCntGbl=0;
uint32_t AstUser1InUse::s_userCntGbl=0;	// Hot cache line, leave adjacent
uint32_t AstUser2InUse::s_userCntGbl=0;	// Hot cache line, leave adjacent
uint32_t AstUser3InUse::s_userCntGbl=0;	// Hot cache line, leave adjacent
uint32_t AstUser4InUse::s_userCntGbl=0;	// Hot cache line, leave adjacent
uint32_t AstUser5InUse::s_userCntGbl=0;	// Hot cache line, leave adjacent

bool AstUser1InUse::s_userBusy=false;
bool AstUser2InUse::s_userBusy=false;
bool AstUser3InUse::s_userBusy=false;
bool AstUser4InUse::s_userBusy=false;
bool AstUser5InUse::s_userBusy=false;

int AstNodeDType::s_uniqueNum = 0;


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
    m_dtypep = NULL;
    m_clonep = NULL;
    m_cloneCnt = 0;
    // Attributes
    m_didWidth = false;
    m_doingWidth = false;
    m_user1p = NULL;
    m_user1Cnt = 0;
    m_user2p = NULL;
    m_user2Cnt = 0;
    m_user3p = NULL;
    m_user3Cnt = 0;
    m_user4p = NULL;
    m_user4Cnt = 0;
    m_user5p = NULL;
    m_user5Cnt = 0;
}

string AstNode::encodeName(const string& namein) {
    // Encode signal name raw from parser, then not called again on same signal
    const char* start = namein.c_str();
    string out;
    for (const char* pos = start; *pos; pos++) {
	if ((pos==start) ? isalpha(pos[0])  // digits can't lead identifiers
	    : isalnum(pos[0])) {
	    out += pos[0];
	} else if (pos[0]=='_') {
	    if (pos[1]=='_') {
		out += "_"; out += "__05F";  // hex(_) = 0x5F
		pos++;
	    } else {
		out += pos[0];
	    }
	} else {
	    // Need the leading 0 so this will never collide with
	    // a user identifier nor a temp we create in Verilator.
	    // We also do *NOT* use __DOT__ etc, as we search for those
	    // in some replacements, and don't want to mangle the user's names.
	    char hex[10]; sprintf(hex,"__0%02X",pos[0]);
	    out += hex;
	}
    }
    return out;
}

string AstNode::encodeNumber(vlsint64_t num) {
    if (num < 0) {
	return "__02D"+cvtToStr(-num);  // 2D=-
    } else {
	return cvtToStr(num);
    }
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

string AstNode::vcdName(const string& namein) {
    // VCD tracing expects space to separate hierarchy
    // Dots are reserved for dots the user put in the name
    string pretty = namein;
    string::size_type pos;
    while ((pos=pretty.find("__DOT__")) != string::npos) {
	pretty.replace(pos, 7, " ");
    }
    while ((pos=pretty.find(".")) != string::npos) {
	pretty.replace(pos, 1, " ");
    }
    // Now convert escaped special characters, etc
    return prettyName(pretty);
}

string AstNode::prettyName(const string& namein) {
    string pretty;
    pretty = "";
    for (const char* pos = namein.c_str(); *pos; ) {
	if (0==strncmp(pos,"__BRA__",7)) {
	    pretty += "[";
	    pos += 7;
	}
	else if (0==strncmp(pos,"__KET__",7)) {
	    pretty += "]";
	    pos += 7;
	}
	else if (0==strncmp(pos,"__DOT__",7)) {
	    pretty += ".";
	    pos += 7;
	}
	else if (0==strncmp(pos,"->",2)) {
	    pretty += ".";
	    pos += 2;
	}
	else if (0==strncmp(pos,"__PVT__",7)) {
	    pretty += "";
	    pos += 7;
	}
	else if (pos[0]=='_' && pos[1]=='_' && pos[2]=='0'
		 && isxdigit(pos[3]) && isxdigit(pos[4])) {
	    char value = 0;
	    value += 16*(isdigit(pos[3]) ? (pos[3]-'0') : (tolower(pos[3])-'a'+10));
	    value +=    (isdigit(pos[4]) ? (pos[4]-'0') : (tolower(pos[4])-'a'+10));
	    pretty += value;
	    pos += 5;
	}
	else {
	    pretty += pos[0];
	    pos++;
	}
    }
    if (pretty.substr(0,4) == "TOP.") pretty.replace(0,4,"");
    if (pretty.substr(0,5) == "TOP->") pretty.replace(0,5,"");
    return pretty;
}

string AstNode::prettyTypeName() const {
    if (name()=="") return typeName();
    return string(typeName())+" '"+prettyName()+"'";
}

//######################################################################
// Insertion

inline void AstNode::debugTreeChange(const char* prefix, int lineno, bool next) {
#ifdef VL_DEBUG
    // Called on all major tree changers.
    // Only for use for those really nasty bugs relating to internals
    // Note this may be null.
    //if (debug()) cout<<"-treeChange: V3Ast.cpp:"<<lineno<<" Tree Change for "<<prefix<<": "<<(void*)this<<" <e"<<AstNode::s_editCntGbl<<">"<<endl;
    //if (debug()) {
    //	cout<<"-treeChange: V3Ast.cpp:"<<lineno<<" Tree Change for "<<prefix<<endl;
    //	// Commenting out the section below may crash, as the tree state
    //	// between edits is not always consistent for printing
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

void AstNRelinker::dump(ostream& str) const {
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
	// This adds a unfortunate hot 8 bytes to every AstNode, but is faster than passing
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

void AstNode::addHereThisAsNext (AstNode* newp) {
    // {old}->this->{next} becomes {old}->new->this->{next}
    AstNRelinker handle;
    this->unlinkFrBackWithNext(&handle);
    newp->addNext(this);
    handle.relink(newp);
}

void AstNode::swapWith (AstNode* bp) {
    AstNRelinker aHandle;
    AstNRelinker bHandle;
    this->unlinkFrBack(&aHandle);
    bp->unlinkFrBack(&bHandle);
    aHandle.relink(bp);
    bHandle.relink(this);
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
    for (AstNode* nodep=this, *nnextp; nodep; nodep=nnextp) {
	nnextp = nodep->m_nextp;
	// MUST be depth first!
	nodep->m_op1p->deleteTreeIter();
	nodep->m_op2p->deleteTreeIter();
	nodep->m_op3p->deleteTreeIter();
	nodep->m_op4p->deleteTreeIter();
	nodep->m_nextp = NULL;
	nodep->m_backp = NULL;
	nodep->deleteNode();
    }
}

void AstNode::deleteTree() {
    // deleteTree always deletes the next link, because you must have called
    // unlinkFromBack or unlinkFromBackWithNext as appropriate before calling this.
    if (!this) return;
    UASSERT(m_backp==NULL,"Delete called on node with backlink still set\n");
    this->debugTreeChange("-delTree:  ", __LINE__, true);
    this->editCountInc();
    // MUST be depth first!
    deleteTreeIter();
}

//======================================================================
// Memory checks

#ifdef VL_LEAK_CHECKS
void* AstNode::operator new(size_t size) {
    AstNode* objp = static_cast<AstNode*>(::operator new(size));
    V3Broken::addNewed(objp);
    return objp;
}

void AstNode::operator delete(void* objp, size_t size) {
    if (!objp) return;
    AstNode* nodep = static_cast<AstNode*>(objp);
    V3Broken::deleted(nodep);
    ::operator delete(objp);
}
#endif

//======================================================================
// Iterators

void AstNode::iterateChildren(AstNVisitor& v, AstNUser* vup) {
    // This is a very hot function
    if (!this) return;
    ASTNODE_PREFETCH(m_op1p);
    ASTNODE_PREFETCH(m_op2p);
    ASTNODE_PREFETCH(m_op3p);
    ASTNODE_PREFETCH(m_op4p);
    // if () not needed since iterateAndNext accepts null this, but faster with it.
    if (m_op1p) m_op1p->iterateAndNext(v, vup);
    if (m_op2p) m_op2p->iterateAndNext(v, vup);
    if (m_op3p) m_op3p->iterateAndNext(v, vup);
    if (m_op4p) m_op4p->iterateAndNext(v, vup);
}

void AstNode::iterateChildrenConst(AstNVisitor& v, AstNUser* vup) {
    // This is a very hot function
    if (!this) return;
    ASTNODE_PREFETCH(m_op1p);
    ASTNODE_PREFETCH(m_op2p);
    ASTNODE_PREFETCH(m_op3p);
    ASTNODE_PREFETCH(m_op4p);
    // if () not needed since iterateAndNext accepts null this, but faster with it.
    if (m_op1p) m_op1p->iterateAndNextConst(v, vup);
    if (m_op2p) m_op2p->iterateAndNextConst(v, vup);
    if (m_op3p) m_op3p->iterateAndNextConst(v, vup);
    if (m_op4p) m_op4p->iterateAndNextConst(v, vup);
}

void AstNode::iterateAndNext(AstNVisitor& v, AstNUser* vup) {
    // This is a very hot function
    // IMPORTANT: If you replace a node that's the target of this iterator,
    // then the NEW node will be iterated on next, it isn't skipped!
    // if (!this) return;  // Part of for()
    // Future versions of this function may require the node to have a back to be iterated;
    // there's no lower level reason yet though the back must exist.
    AstNode* nodep=this;
#ifdef VL_DEBUG  // Otherwise too hot of a function for debug
    if (VL_UNLIKELY(nodep && !nodep->m_backp)) nodep->v3fatalSrc("iterateAndNext node has no back");
#endif
    while (nodep) {
	AstNode* niterp = nodep;  // This address may get stomped via m_iterpp if the node is edited
	ASTNODE_PREFETCH(nodep->m_nextp);
	// Desirable check, but many places where multiple iterations are OK
	//if (VL_UNLIKELY(niterp->m_iterpp)) niterp->v3fatalSrc("IterateAndNext under iterateAndNext may miss edits");
	// cppcheck-suppress nullPointer
	niterp->m_iterpp = &niterp;
	niterp->accept(v, vup);
	// accept may do a replaceNode and change niterp on us...
	//if (niterp != nodep) UINFO(1,"iterateAndNext edited "<<(void*)nodep<<" now into "<<(void*)niterp<<endl);  // niterp maybe NULL, so need cast
	if (!niterp) return;  // Perhaps node deleted inside accept
	niterp->m_iterpp = NULL;
	if (VL_UNLIKELY(niterp!=nodep)) { // Edited node inside accept
	    nodep = niterp;
	} else {  // Unchanged node, just continue loop
	    nodep = niterp->m_nextp;
	}
    }
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

void AstNode::iterateAndNextConst(AstNVisitor& v, AstNUser* vup) {
    // Keep following the current list even if edits change it
    if (!this) return;
    for (AstNode* nodep=this; nodep; ) {
	AstNode* nnextp = nodep->m_nextp;
	ASTNODE_PREFETCH(nnextp);
	nodep->accept(v, vup);
	nodep = nnextp;
    }
}

AstNode* AstNode::acceptSubtreeReturnEdits(AstNVisitor& v, AstNUser* vup) {
    // Some visitors perform tree edits (such as V3Const), and may even
    // replace/delete the exact nodep that the visitor is called with.  If
    // this happens, the parent will lose the handle to the node that was
    // processed.
    // To solve this, this function returns the pointer to the replacement node,
    // which in many cases is just the same node that was passed in.
    AstNode* nodep = this;  // Note "this" may point to bogus point later in this function
    if (nodep->castNetlist()) {
	// Calling on top level; we know the netlist won't get replaced
	nodep->accept(v, vup);
    } else if (!nodep->backp()) {
	// Calling on standalone tree; insert a shim node so we can keep track, then delete it on completion
	AstBegin* tempp = new AstBegin(nodep->fileline(),"[EditWrapper]",nodep);
	{
	    tempp->stmtsp()->accept(v, vup);  nodep=NULL; // nodep to null as may be replaced
	}
	nodep = tempp->stmtsp()->unlinkFrBackWithNext();
	tempp->deleteTree(); tempp=NULL;
    } else {
	// Use back to determine who's pointing at us (IE assume new node grafts into same place as old one)
	AstNode** nextnodepp = NULL;
	if (this->m_backp->m_op1p == this) nextnodepp = &(this->m_backp->m_op1p);
	else if (this->m_backp->m_op2p == this) nextnodepp = &(this->m_backp->m_op2p);
	else if (this->m_backp->m_op3p == this) nextnodepp = &(this->m_backp->m_op3p);
	else if (this->m_backp->m_op4p == this) nextnodepp = &(this->m_backp->m_op4p);
	else if (this->m_backp->m_nextp == this) nextnodepp = &(this->m_backp->m_nextp);
	if (!nextnodepp) this->v3fatalSrc("Node's back doesn't point to forward to node itself");
	{
	    nodep->accept(v, vup); nodep=NULL; // nodep to null as may be replaced
	}
	nodep = *nextnodepp;  // Grab new node from point where old was connected
    }
    return nodep;
}

//======================================================================

void AstNode::cloneRelinkTree() {
    if (!this) return;
    for (AstNode* nodep=this; nodep; nodep=nodep->m_nextp) {
	if (m_dtypep && m_dtypep->clonep()) {
	    m_dtypep = m_dtypep->clonep()->castNodeDType();
	}
	nodep->cloneRelink();
	nodep->m_op1p->cloneRelinkTree();
	nodep->m_op2p->cloneRelinkTree();
	nodep->m_op3p->cloneRelinkTree();
	nodep->m_op4p->cloneRelinkTree();
    }
}

//======================================================================
// Comparison

bool AstNode::sameTreeIter(AstNode* node2p, bool ignNext, bool gateOnly) {
    // Return true if the two trees are identical
    if (this==NULL && node2p==NULL) return true;
    if (this==NULL || node2p==NULL) return false;
    if (this->type() != node2p->type()
	|| this->dtypep() != node2p->dtypep()
	|| !this->same(node2p)
	|| (gateOnly && !this->isGateOptimizable())) {
	return false;
    }
    return (this->op1p()->sameTreeIter(node2p->op1p(),false,gateOnly)
	    && this->op2p()->sameTreeIter(node2p->op2p(),false,gateOnly)
	    && this->op3p()->sameTreeIter(node2p->op3p(),false,gateOnly)
	    && this->op4p()->sameTreeIter(node2p->op4p(),false,gateOnly)
	    && (ignNext || this->nextp()->sameTreeIter(node2p->nextp(),false,gateOnly))
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
    for (string::const_iterator it = name.begin(); it!=name.end(); ++it) {
	val = val*31 + *it;
    }
    setBoth(1,val);
}

//======================================================================
// Debugging

void AstNode::checkTreeIter(AstNode* backp) {
    if (backp != this->backp()) {
	this->v3fatalSrc("Back node inconsistent");
    }
    if (castNodeTermop() || castNodeVarRef()) {
	// Termops have a short-circuited iterateChildren, so check usage
	if (op1p()||op2p()||op3p()||op4p())
	    this->v3fatalSrc("Terminal operation with non-terminals");
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

void AstNode::dumpGdb() {  // For GDB only
    if (!this) { cout<<"This=NULL"<<endl; return; }
    dumpGdbHeader();
    cout<<"  "; dump(cout); cout<<endl;
}
void AstNode::dumpGdbHeader() const {  // For GDB only
    if (!this) { cout<<"This=NULL"<<endl; return; }
    dumpPtrs(cout);
    cout<<"  Fileline = "<<fileline()<<endl;
}
void AstNode::dumpTreeGdb() {  // For GDB only
    if (!this) { cout<<"This=NULL"<<endl; return; }
    dumpGdbHeader();
    dumpTree(cout);
}
void AstNode::dumpTreeFileGdb(const char* filenamep) {  // For GDB only
    string filename = filenamep ? filenamep : v3Global.debugFilename("debug.tree",98);
    v3Global.rootp()->dumpTreeFile(filename);
}

void AstNode::checkIter() const {
    if (m_iterpp) {
	dumpPtrs(cout);
	// Perhaps something forgot to clear m_iterpp?
	this->v3fatalSrc("Iteration link should be NULL");
    }
}

void AstNode::dumpPtrs(ostream& os) const {
    os<<"This="<<typeName()<<" "<<(void*)this;
    os<<" back="<<(void*)backp();
    if (nextp()) os<<" next="<<(void*)nextp();
    if (m_headtailp==this) os<<" headtail=this";
    else os<<" headtail="<<(void*)m_headtailp;
    if (op1p()) os<<" op1p="<<(void*)op1p();
    if (op2p()) os<<" op2p="<<(void*)op2p();
    if (op3p()) os<<" op3p="<<(void*)op3p();
    if (op4p()) os<<" op4p="<<(void*)op4p();
    if (user1p()) os<<" user1p="<<(void*)user1p();
    if (user2p()) os<<" user2p="<<(void*)user2p();
    if (user3p()) os<<" user3p="<<(void*)user3p();
    if (user4p()) os<<" user4p="<<(void*)user4p();
    if (user5p()) os<<" user5p="<<(void*)user5p();
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

void AstNode::dumpTreeFile(const string& filename, bool append, bool doDump) {
    if (doDump) {
	{   // Write log & close
	    UINFO(2,"Dumping "<<filename<<endl);
	    const auto_ptr<ofstream> logsp (V3File::new_ofstream(filename, append));
	    if (logsp->fail()) v3fatalSrc("Can't write "<<filename);
	    *logsp<<"Verilator Tree Dump (format 0x3900) from <e"<<dec<<editCountLast()<<">";
	    *logsp<<" to <e"<<dec<<editCountGbl()<<">"<<endl;
	    if (editCountGbl()==editCountLast()
		&& !(v3Global.opt.dumpTree()>=9)) {
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

void AstNode::v3errorEnd(ostringstream& str) const {
    if (this && m_fileline) {
	ostringstream nsstr;
	nsstr<<str.str();
	if (debug()) {
	    nsstr<<endl;
	    nsstr<<"-node: "; ((AstNode*)this)->dump(nsstr); nsstr<<endl;
	}
	m_fileline->v3errorEnd(nsstr);
    } else {
	V3Error::v3errorEnd(str);
    }
}

string AstNode::warnMore() const {
    if (this) return this->fileline()->warnMore();
    else return V3Error::warnMore();
}

//======================================================================
// Data type conversion

void AstNode::dtypeChgSigned(bool flag) {
    if (!dtypep()) this->v3fatalSrc("No dtype when changing to (un)signed");
    dtypeChgWidthSigned(dtypep()->width(), dtypep()->widthMin(),
			flag ? AstNumeric::SIGNED : AstNumeric::UNSIGNED);
}
void AstNode::dtypeChgWidth(int width, int widthMin) {
    if (!dtypep()) this->v3fatalSrc("No dtype when changing width");  // Use ChgWidthSigned(...UNSIGNED) otherwise
    dtypeChgWidthSigned(width, widthMin, dtypep()->numeric());
}

void AstNode::dtypeChgWidthSigned(int width, int widthMin, AstNumeric numeric) {
    if (!dtypep()) {
	// We allow dtypep() to be null, as before/during widthing dtypes are not resolved
	dtypeSetLogicSized(width, widthMin, numeric);
    } else {
	if (width==dtypep()->width()
	    && widthMin==dtypep()->widthMin()
	    && numeric==dtypep()->numeric()) return;  // Correct already
	// FUTURE: We may be pointing at a two state data type, and this may
	// convert it to logic.  Since the AstVar remains correct, we
	// work OK but this assumption may break in the future.
	// Note we can't just clone and do a widthForce, as if it's a BasicDType
	// the msb() indications etc will be incorrect.
	dtypeSetLogicSized(width, widthMin, numeric);
    }
}

AstNodeDType* AstNode::findBasicDType(AstBasicDTypeKwd kwd) const {
    // For 'simple' types we use the global directory.  These are all unsized.
    // More advanced types land under the module/task/etc
    return v3Global.rootp()->typeTablep()
	->findBasicDType(fileline(), kwd);
}
AstNodeDType* AstNode::findBitDType(int width, int widthMin, AstNumeric numeric) const {
    return v3Global.rootp()->typeTablep()
	->findLogicBitDType(fileline(), AstBasicDTypeKwd::BIT, width, widthMin, numeric);
}
AstNodeDType* AstNode::findLogicDType(int width, int widthMin, AstNumeric numeric) const {
    return v3Global.rootp()->typeTablep()
	->findLogicBitDType(fileline(), AstBasicDTypeKwd::LOGIC, width, widthMin, numeric);
}
AstNodeDType* AstNode::findLogicRangeDType(VNumRange range, int widthMin, AstNumeric numeric) const {
    return v3Global.rootp()->typeTablep()
	->findLogicBitDType(fileline(), AstBasicDTypeKwd::LOGIC, range, widthMin, numeric);
}
AstBasicDType* AstNode::findInsertSameDType(AstBasicDType* nodep) {
    return v3Global.rootp()->typeTablep()
	->findInsertSameDType(nodep);
}

//######################################################################
// AstNVisitor

void AstNVisitor::doDeletes() {
    for (vector<AstNode*>::iterator it = m_deleteps.begin(); it != m_deleteps.end(); ++it) {
	(*it)->deleteTree();
    }
    m_deleteps.clear();
}
