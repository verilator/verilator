// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include "V3Broken.h"
#include "V3EmitV.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3String.h"

#include <iomanip>
#include <memory>

//======================================================================
// Statics

uint64_t AstNode::s_editCntLast = 0;
uint64_t AstNode::s_editCntGbl = 0;  // Hot cache line

// To allow for fast clearing of all user pointers, we keep a "timestamp"
// along with each userp, and thus by bumping this count we can make it look
// as if we iterated across the entire tree to set all the userp's to null.
int AstNode::s_cloneCntGbl = 0;
uint32_t VNUser1InUse::s_userCntGbl = 0;  // Hot cache line, leave adjacent
uint32_t VNUser2InUse::s_userCntGbl = 0;  // Hot cache line, leave adjacent
uint32_t VNUser3InUse::s_userCntGbl = 0;  // Hot cache line, leave adjacent
uint32_t VNUser4InUse::s_userCntGbl = 0;  // Hot cache line, leave adjacent
uint32_t VNUser5InUse::s_userCntGbl = 0;  // Hot cache line, leave adjacent

bool VNUser1InUse::s_userBusy = false;
bool VNUser2InUse::s_userBusy = false;
bool VNUser3InUse::s_userBusy = false;
bool VNUser4InUse::s_userBusy = false;
bool VNUser5InUse::s_userBusy = false;

int AstNodeDType::s_uniqueNum = 0;

//######################################################################
// V3AstType

std::ostream& operator<<(std::ostream& os, VNType rhs);

//######################################################################
// Creators

AstNode::AstNode(VNType t, FileLine* fl)
    : m_type{t}
    , m_fileline{fl} {
    m_headtailp = this;  // When made, we're a list of only a single element
    // Attributes
    m_flags.didWidth = false;
    m_flags.doingWidth = false;
    m_flags.protect = true;
    m_flags.unused = 0;  // Initializing this avoids a read-modify-write on construction
    editCountInc();
}

AstNode* AstNode::abovep() const {
    // m_headtailp only valid at beginning or end of list
    // Avoid supporting at other locations as would require walking
    // list which is likely to cause performance issues.
    UASSERT_OBJ(!m_nextp || firstAbovep(), this, "abovep() not allowed when in midlist");
    const AstNode* const firstp = firstAbovep() ? this : m_headtailp;
    return firstp->backp();
}

string AstNode::encodeName(const string& namein) {
    // Encode signal name raw from parser, then not called again on same signal
    string out;
    for (string::const_iterator pos = namein.begin(); pos != namein.end(); ++pos) {
        if ((pos == namein.begin()) ? isalpha(pos[0])  // digits can't lead identifiers
                                    : isalnum(pos[0])) {
            out += pos[0];
        } else if (pos[0] == '_') {
            if (pos[1] == '_') {
                out += "_";
                out += "__05F";  // hex(_) = 0x5F
                ++pos;
                if (pos == namein.end()) break;
            } else {
                out += pos[0];
            }
        } else {
            // Need the leading 0 so this will never collide with
            // a user identifier nor a temp we create in Verilator.
            // We also do *NOT* use __DOT__ etc, as we search for those
            // in some replacements, and don't want to mangle the user's names.
            const unsigned val = pos[0] & 0xff;  // Mask to avoid sign extension
            std::stringstream hex;
            hex << std::setfill('0') << std::setw(2) << std::hex << val;
            out += "__0" + hex.str();
        }
    }
    // Shorten names
    // TODO long term use VName in place of "string name"
    // Then we also won't need to save the table of hased values
    VName vname{out};
    return vname.hashedName();
}

string AstNode::encodeNumber(int64_t num) {
    if (num < 0) {
        return "__02D" + cvtToStr(-num);  // 2D=-
    } else {
        return cvtToStr(num);
    }
}

string AstNode::nameProtect() const { return VIdProtect::protectIf(name(), protect()); }
string AstNode::origNameProtect() const { return VIdProtect::protectIf(origName(), protect()); }

string AstNode::shortName() const {
    string pretty = name();
    string::size_type pos;
    while ((pos = pretty.find("__PVT__")) != string::npos) pretty.replace(pos, 7, "");
    return pretty;
}

string AstNode::dedotName(const string& namein) {
    string pretty = namein;
    string::size_type pos;
    while ((pos = pretty.find("__DOT__")) != string::npos) pretty.replace(pos, 7, ".");
    if (pretty.substr(0, 4) == "TOP.") pretty.replace(0, 4, "");
    return pretty;
}

string AstNode::vcdName(const string& namein) {
    // VCD tracing expects space to separate hierarchy
    // Dots are reserved for dots the user put in the name
    // We earlier hashed all symbols, dehash them so user sees real name
    string pretty{VName::dehash(namein)};
    string::size_type pos;
    while ((pos = pretty.find("__DOT__")) != string::npos) pretty.replace(pos, 7, " ");
    while ((pos = pretty.find('.')) != string::npos) pretty.replace(pos, 1, " ");
    // Now convert escaped special characters, etc
    return prettyName(pretty);
}

string AstNode::prettyName(const string& namein) {
    // This function is somewhat hot, so we short-circuit some compares
    string pretty;
    pretty = "";
    pretty.reserve(namein.length());
    for (const char* pos = namein.c_str(); *pos;) {
        if (pos[0] == '-' && pos[1] == '>') {  // ->
            pretty += ".";
            pos += 2;
            continue;
        }
        if (pos[0] == '_' && pos[1] == '_') {  // Short-circuit
            if (0 == strncmp(pos, "__BRA__", 7)) {
                pretty += "[";
                pos += 7;
                continue;
            }
            if (0 == strncmp(pos, "__KET__", 7)) {
                pretty += "]";
                pos += 7;
                continue;
            }
            if (0 == strncmp(pos, "__DOT__", 7)) {
                pretty += ".";
                pos += 7;
                continue;
            }
            if (0 == strncmp(pos, "__PVT__", 7)) {
                pretty += "";
                pos += 7;
                continue;
            }
            if (pos[0] == '_' && pos[1] == '_' && pos[2] == '0' && isxdigit(pos[3])
                && isxdigit(pos[4])) {
                char value = 0;
                value += 16 * (isdigit(pos[3]) ? (pos[3] - '0') : (tolower(pos[3]) - 'a' + 10));
                value += (isdigit(pos[4]) ? (pos[4] - '0') : (tolower(pos[4]) - 'a' + 10));
                pretty += value;
                pos += 5;
                continue;
            }
        }
        // Default
        pretty += pos[0];
        ++pos;
    }
    if (pretty[0] == 'T' && pretty.substr(0, 4) == "TOP.") pretty.replace(0, 4, "");
    if (pretty[0] == 'T' && pretty.substr(0, 5) == "TOP->") pretty.replace(0, 5, "");
    return pretty;
}

string AstNode::prettyTypeName() const {
    if (name() == "") return typeName();
    return std::string{typeName()} + " '" + prettyName() + "'";
}

//######################################################################
// Insertion

inline void AstNode::debugTreeChange(const AstNode* nodep, const char* prefix, int lineno,
                                     bool next) {
#ifdef VL_DEBUG
// Called on all major tree changers.
// Only for use for those really nasty bugs relating to internals
// Note this may be null.
// if (debug()) cout<<"-treeChange: V3Ast.cpp:"<<lineno<<" Tree Change for "
//                 <<prefix<<": "<<cvtToHex(this)<<" <e"<<AstNode::s_editCntGbl<<">"<<endl;
// if (debug()) {
//  cout<<"-treeChange: V3Ast.cpp:"<<lineno<<" Tree Change for "<<prefix<<endl;
//  // Commenting out the section below may crash, as the tree state
//  // between edits is not always consistent for printing
//  cout<<"-treeChange: V3Ast.cpp:"<<lineno<<" Tree Change for "<<prefix<<endl;
//  v3Global.rootp()->dumpTree(cout, "-treeChange: ");
//  if (next||1) this->dumpTreeAndNext(cout, prefix);
//  else this->dumpTree(cout, prefix);
//  this->checkTree();
//  v3Global.rootp()->checkTree();
//}
#endif
}

template <>
AstNode* AstNode::addNext<AstNode, AstNode>(AstNode* nodep, AstNode* newp) {
    // Add to m_nextp, returns this
    UDEBUGONLY(UASSERT_OBJ(newp, nodep, "Null item passed to addNext"););
    debugTreeChange(nodep, "-addNextThs: ", __LINE__, false);
    debugTreeChange(newp, "-addNextNew: ", __LINE__, true);
    if (!nodep) {  // verilog.y and lots of other places assume this
        return newp;
    } else {
        // Find end of old list
        AstNode* oldtailp = nodep;
        if (oldtailp->m_nextp) {
            if (oldtailp->m_headtailp) {
                oldtailp = oldtailp->m_headtailp;  // This=beginning of list, jump to end
                UDEBUGONLY(UASSERT_OBJ(!oldtailp->m_nextp, nodep,
                                       "Node had next, but headtail says it shouldn't"););
            } else {
                // Though inefficient, we are occasionally passed an
                // addNext in the middle of a list.
                while (oldtailp->m_nextp) oldtailp = oldtailp->m_nextp;
            }
        }
        // Link it in
        oldtailp->m_nextp = newp;
        newp->m_backp = oldtailp;
        // New tail needs the head
        AstNode* const newtailp = newp->m_headtailp;
        AstNode* const headp = oldtailp->m_headtailp;
        oldtailp->m_headtailp = nullptr;  // May be written again as new head
        newp->m_headtailp = nullptr;  // May be written again as new tail
        newtailp->m_headtailp = headp;
        headp->m_headtailp = newtailp;
        newp->editCountInc();
        if (oldtailp->m_iterpp) *(oldtailp->m_iterpp) = newp;  // Iterate on new item
    }
    debugTreeChange(nodep, "-addNextOut:", __LINE__, true);
    return nodep;
}

template <>
AstNode* AstNode::addNextNull<AstNode, AstNode>(AstNode* nodep, AstNode* newp) {
    if (!newp) return nodep;
    return addNext(nodep, newp);
}

void AstNode::addNextHere(AstNode* newp) {
    // Add to m_nextp on exact node passed, not at the end.
    //  This could be at head, tail, or both (single)
    //  New  could be head of single node, or list
    UASSERT(newp, "Null item passed to addNext");
    UASSERT_OBJ(!newp->backp(), newp, "New node (back) already assigned?");
    debugTreeChange(this, "-addHereThs: ", __LINE__, false);
    debugTreeChange(newp, "-addHereNew: ", __LINE__, true);
    newp->editCountInc();

    AstNode* const addlastp = newp->m_headtailp;  // Last node in list to be added
    UASSERT_OBJ(!addlastp->m_nextp, addlastp, "Headtailp tail isn't at the tail");

    // Forward links
    AstNode* const oldnextp = this->m_nextp;
    this->m_nextp = newp;
    addlastp->m_nextp = oldnextp;  // Perhaps null if 'this' is not list

    // Backward links
    if (oldnextp) oldnextp->m_backp = addlastp;
    newp->m_backp = this;

    // Head/tail
    AstNode* const oldheadtailp = this->m_headtailp;
    //    (!oldheadtailp)               // this was&is middle of list
    //    (oldheadtailp==this && !oldnext)// this was head AND tail (one node long list)
    //    (oldheadtailp && oldnextp)    // this was&is head of list of not just one node, not
    //    tail (oldheadtailp && !oldnextp)   // this was tail of list, might also
    //                                     be head of one-node list
    //
    newp->m_headtailp = nullptr;  // Not at head any longer
    addlastp->m_headtailp = nullptr;  // Presume middle of list
    // newp might happen to be head/tail after all, if so will be set again below
    if (oldheadtailp) {  // else in middle of list, no change
        if (oldheadtailp == this) {  // this was one node
            this->m_headtailp = addlastp;  // Was head/tail, now a tail
            addlastp->m_headtailp = oldheadtailp;  // Tail needs to remember head (or nullptr)
        } else if (!oldnextp) {  // this was tail
            this->m_headtailp = nullptr;  // No longer a tail
            oldheadtailp->m_headtailp = addlastp;  // Head gets new tail
            addlastp->m_headtailp = oldheadtailp;  // Tail needs to remember head (or nullptr)
        }  // else is head, and we're inserting into the middle, so no other change
    }

    if (this->m_iterpp) *(this->m_iterpp) = newp;  // Iterate on new item
    debugTreeChange(this, "-addHereOut: ", __LINE__, true);
}

void AstNode::setOp1p(AstNode* newp) {
    UASSERT(newp, "Null item passed to setOp1p");
    UDEBUGONLY(UASSERT_OBJ(!m_op1p, this, "Adding to non-empty, non-list op1"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_nextp, newp, "Adding list to non-list op1"););
    debugTreeChange(this, "-setOp1pThs: ", __LINE__, false);
    debugTreeChange(newp, "-setOp1pNew: ", __LINE__, true);
    m_op1p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    debugTreeChange(this, "-setOp1pOut: ", __LINE__, false);
}

void AstNode::setOp2p(AstNode* newp) {
    UASSERT(newp, "Null item passed to setOp2p");
    UDEBUGONLY(UASSERT_OBJ(!m_op2p, this, "Adding to non-empty, non-list op2"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_nextp, newp, "Adding list to non-list op2"););
    debugTreeChange(this, "-setOp2pThs: ", __LINE__, false);
    debugTreeChange(newp, "-setOp2pNew: ", __LINE__, true);
    m_op2p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    debugTreeChange(this, "-setOp2pOut: ", __LINE__, false);
}

void AstNode::setOp3p(AstNode* newp) {
    UASSERT(newp, "Null item passed to setOp3p");
    UDEBUGONLY(UASSERT_OBJ(!m_op3p, this, "Adding to non-empty, non-list op3"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_nextp, newp, "Adding list to non-list op3"););
    debugTreeChange(this, "-setOp3pThs: ", __LINE__, false);
    debugTreeChange(newp, "-setOp3pNew: ", __LINE__, true);
    m_op3p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    debugTreeChange(this, "-setOp3pOut: ", __LINE__, false);
}

void AstNode::setOp4p(AstNode* newp) {
    UASSERT(newp, "Null item passed to setOp4p");
    UDEBUGONLY(UASSERT_OBJ(!m_op4p, this, "Adding to non-empty, non-list op4"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    UDEBUGONLY(UASSERT_OBJ(!newp->m_nextp, newp, "Adding list to non-list op4"););
    debugTreeChange(this, "-setOp4pThs: ", __LINE__, false);
    debugTreeChange(newp, "-setOp4pNew: ", __LINE__, true);
    m_op4p = newp;
    newp->editCountInc();
    newp->m_backp = this;
    debugTreeChange(this, "-setOp4pOut: ", __LINE__, false);
}

void AstNode::addOp1p(AstNode* newp) {
    UASSERT(newp, "Null item passed to addOp1p");
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    if (!m_op1p) {
        op1p(newp);
    } else {
        m_op1p->addNext(newp);
    }
}

void AstNode::addOp2p(AstNode* newp) {
    UASSERT(newp, "Null item passed to addOp2p");
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    if (!m_op2p) {
        op2p(newp);
    } else {
        m_op2p->addNext(newp);
    }
}

void AstNode::addOp3p(AstNode* newp) {
    UASSERT(newp, "Null item passed to addOp3p");
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    if (!m_op3p) {
        op3p(newp);
    } else {
        m_op3p->addNext(newp);
    }
}

void AstNode::addOp4p(AstNode* newp) {
    UASSERT(newp, "Null item passed to addOp4p");
    UDEBUGONLY(UASSERT_OBJ(!newp->m_backp, newp, "Adding already linked node"););
    if (!m_op4p) {
        op4p(newp);
    } else {
        m_op4p->addNext(newp);
    }
}

void AstNode::replaceWith(AstNode* newp) {
    // Replace oldp with this
    // Unlike a unlink/relink, children are changed to point to the new node.
    VNRelinker repHandle;
    this->unlinkFrBack(&repHandle);
    repHandle.relink(newp);
}

void VNRelinker::dump(std::ostream& str) const {
    str << " BK=" << reinterpret_cast<uint32_t*>(m_backp);
    str << " ITER=" << reinterpret_cast<uint32_t*>(m_iterpp);
    str << " CHG=" << (m_chg == RELINK_NEXT ? "[NEXT] " : "");
    str << (m_chg == RELINK_OP1 ? "[OP1] " : "");
    str << (m_chg == RELINK_OP2 ? "[OP2] " : "");
    str << (m_chg == RELINK_OP3 ? "[OP3] " : "");
    str << (m_chg == RELINK_OP4 ? "[OP4] " : "");
}

AstNode* AstNode::unlinkFrBackWithNext(VNRelinker* linkerp) {
    debugTreeChange(this, "-unlinkWNextThs: ", __LINE__, true);
    AstNode* const oldp = this;
    UASSERT_OBJ(oldp->m_backp, oldp, "Node has no back, already unlinked?");
    oldp->editCountInc();
    AstNode* const backp = oldp->m_backp;
    if (linkerp) {
        linkerp->m_oldp = oldp;
        linkerp->m_backp = backp;
        linkerp->m_iterpp = oldp->m_iterpp;
        if (backp->m_nextp == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_NEXT;
        } else if (backp->m_op1p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP1;
        } else if (backp->m_op2p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP2;
        } else if (backp->m_op3p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP3;
        } else if (backp->m_op4p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP4;
        } else {
            oldp->v3fatalSrc("Unlink of node with back not pointing to it.");
        }
    }
    if (backp->m_nextp == oldp) {
        backp->m_nextp = nullptr;
        // Old list gets truncated
        // New list becomes a list upon itself
        // Most common case is unlinking a entire operand tree
        // (else we'd probably call unlinkFrBack without next)
        // We may be in the middle of a list; we have no way to find head or tail!
        AstNode* oldtailp = oldp;
        while (oldtailp->m_nextp) oldtailp = oldtailp->m_nextp;
        // Create new head/tail of old list
        AstNode* const oldheadp = oldtailp->m_headtailp;
        oldheadp->m_headtailp = oldp->m_backp;
        oldheadp->m_headtailp->m_headtailp = oldheadp;
        // Create new head/tail of extracted list
        oldp->m_headtailp = oldtailp;
        oldp->m_headtailp->m_headtailp = oldp;
    } else if (backp->m_op1p == oldp) {
        backp->m_op1p = nullptr;
    } else if (backp->m_op2p == oldp) {
        backp->m_op2p = nullptr;
    } else if (backp->m_op3p == oldp) {
        backp->m_op3p = nullptr;
    } else if (backp->m_op4p == oldp) {
        backp->m_op4p = nullptr;
    } else {
        this->v3fatalSrc("Unlink of node with back not pointing to it.");
    }
    // Relink
    oldp->m_backp = nullptr;
    // Iterator fixup
    if (oldp->m_iterpp) *(oldp->m_iterpp) = nullptr;
    oldp->m_iterpp = nullptr;
    debugTreeChange(oldp, "-unlinkWNextOut: ", __LINE__, true);
    return oldp;
}

AstNode* AstNode::unlinkFrBack(VNRelinker* linkerp) {
    debugTreeChange(this, "-unlinkFrBkThs: ", __LINE__, true);
    AstNode* const oldp = this;
    UASSERT_OBJ(oldp->m_backp, oldp, "Node has no back, already unlinked?");
    oldp->editCountInc();
    AstNode* const backp = oldp->m_backp;
    if (linkerp) {
        linkerp->m_oldp = oldp;
        linkerp->m_backp = backp;
        linkerp->m_iterpp = oldp->m_iterpp;
        if (backp->m_nextp == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_NEXT;
        } else if (backp->m_op1p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP1;
        } else if (backp->m_op2p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP2;
        } else if (backp->m_op3p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP3;
        } else if (backp->m_op4p == oldp) {
            linkerp->m_chg = VNRelinker::RELINK_OP4;
        } else {
            this->v3fatalSrc("Unlink of node with back not pointing to it.");
        }
    }
    if (backp->m_nextp == oldp) {
        // This node gets removed from middle (or tail) of list
        // Not head, since then oldp wouldn't be a next of backp...
        backp->m_nextp = oldp->m_nextp;
        if (backp->m_nextp) backp->m_nextp->m_backp = backp;
        // If it was a tail, back becomes new tail
        if (oldp->m_headtailp) {
            backp->m_headtailp = oldp->m_headtailp;
            backp->m_headtailp->m_headtailp = backp;
        }
    } else {
        if (backp->m_op1p == oldp) {
            backp->m_op1p = oldp->m_nextp;
        } else if (backp->m_op2p == oldp) {
            backp->m_op2p = oldp->m_nextp;
        } else if (backp->m_op3p == oldp) {
            backp->m_op3p = oldp->m_nextp;
        } else if (backp->m_op4p == oldp) {
            backp->m_op4p = oldp->m_nextp;
        } else {
            this->v3fatalSrc("Unlink of node with back not pointing to it.");
        }
        if (oldp->m_nextp) {
            AstNode* const newheadp = oldp->m_nextp;
            newheadp->m_backp = backp;
            newheadp->m_headtailp = oldp->m_headtailp;
            newheadp->m_headtailp->m_headtailp = newheadp;
        }
    }
    // Iterator fixup
    if (oldp->m_iterpp) *(oldp->m_iterpp) = oldp->m_nextp;
    // Relink
    oldp->m_nextp = nullptr;
    oldp->m_backp = nullptr;
    oldp->m_headtailp = this;
    oldp->m_iterpp = nullptr;
    debugTreeChange(oldp, "-unlinkFrBkOut: ", __LINE__, true);
    return oldp;
}

void AstNode::relink(VNRelinker* linkerp) {
    if (debug() > 8) {
        UINFO(0, " EDIT:      relink: ");
        dumpPtrs();
    }
    AstNode* const newp = this;
    UASSERT(linkerp && linkerp->m_backp, "Need non-empty linker");
    UASSERT_OBJ(!newp->m_backp, newp, "New node already linked?");
    newp->editCountInc();

    if (debug() > 8) {
        linkerp->dump(cout);
        cout << endl;
    }

    AstNode* const backp = linkerp->m_backp;
    debugTreeChange(this, "-relinkNew: ", __LINE__, true);
    debugTreeChange(backp, "-relinkTre: ", __LINE__, true);

    switch (linkerp->m_chg) {
    case VNRelinker::RELINK_NEXT: backp->addNextHere(newp); break;
    case VNRelinker::RELINK_OP1: relinkOneLink(backp->m_op1p /*ref*/, newp); break;
    case VNRelinker::RELINK_OP2: relinkOneLink(backp->m_op2p /*ref*/, newp); break;
    case VNRelinker::RELINK_OP3: relinkOneLink(backp->m_op3p /*ref*/, newp); break;
    case VNRelinker::RELINK_OP4: relinkOneLink(backp->m_op4p /*ref*/, newp); break;
    default: this->v3fatalSrc("Relink of node without any link to change."); break;
    }
    // Relink
    newp->m_backp = backp;
    linkerp->m_backp = nullptr;
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
    linkerp->m_backp = nullptr;
    debugTreeChange(this, "-relinkOut: ", __LINE__, true);
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
        AstNode* const newlistlastp = newp->m_headtailp;
        UASSERT_OBJ(!(newlistlastp->m_nextp && newlistlastp != newp), newp,
                    "Headtailp tail isn't at the tail");
        AstNode* const oldlistlastp = pointpr->m_headtailp;
        UASSERT_OBJ(!(oldlistlastp->m_nextp && oldlistlastp != pointpr), newp,
                    "Old headtailp tail isn't at the tail");
        // Next links
        newlistlastp->m_nextp = pointpr;
        pointpr->m_backp = newlistlastp;
        // Head/tail
        pointpr->m_headtailp = nullptr;  // Old head
        newlistlastp->m_headtailp = nullptr;  // Old tail
        newp->m_headtailp = oldlistlastp;  // Head points to tail
        oldlistlastp->m_headtailp = newp;  // Tail points to head
    }
    pointpr = newp;
}

void AstNode::addHereThisAsNext(AstNode* newp) {
    // {back}->this->{next} becomes {back}->new->this->{next}
    UASSERT_OBJ(!newp->backp(), newp, "New node already linked?");
    UASSERT_OBJ(this->m_backp, this, "'this' node has no back, already unlinked?");
    UASSERT_OBJ(newp->m_headtailp, newp, "m_headtailp not set on new node");
    //
    AstNode* const backp = this->m_backp;
    AstNode* const newLastp = newp->m_headtailp;
    //
    this->editCountInc();
    // Common linkage
    newLastp->m_nextp = this;
    this->m_backp = newLastp;
    newp->m_backp = backp;
    // newLastp will not be the last node in the list as 'this' will follow it.
    // If newLastp == newp, then below handles newp becoming head
    newLastp->m_headtailp = nullptr;
    // Linkage dependent on position
    if (backp && backp->m_nextp == this) {
        // If 'this' is not at the head of a list, then the new node will also not be at the head
        // of a list, so we can just link in the new node in the middle.
        backp->m_nextp = newp;
        newp->m_headtailp = nullptr;
    } else {
        // If 'this' is at the head of a list, then the new node becomes the head of that list.
        if (backp) {
            if (backp->m_op1p == this) {
                backp->m_op1p = newp;
            } else if (backp->m_op2p == this) {
                backp->m_op2p = newp;
            } else if (backp->m_op3p == this) {
                backp->m_op3p = newp;
            } else {
                UASSERT_OBJ(backp->m_op4p == this, this, "Don't know where newp should go");
                backp->m_op4p = newp;
            }
        }
        // We also need to update m_headtailp.
        AstNode* const tailp = this->m_headtailp;
        this->m_headtailp = nullptr;
        newp->m_headtailp = tailp;
        tailp->m_headtailp = newp;
    }
    // Iterator fixup
    if (newLastp->m_iterpp) *(newLastp->m_iterpp) = this;
    if (this->m_iterpp) {
        *(this->m_iterpp) = newp;
        this->m_iterpp = nullptr;
    }
    //
    debugTreeChange(this, "-addHereThisAsNext: ", __LINE__, true);
}

void AstNode::swapWith(AstNode* bp) {
    VNRelinker aHandle;
    VNRelinker bHandle;
    this->unlinkFrBack(&aHandle);
    bp->unlinkFrBack(&bHandle);
    aHandle.relink(bp);
    bHandle.relink(this);
}

//======================================================================
// Clone

AstNode* AstNode::cloneTreeIter() {
    // private: Clone single node and children
    AstNode* const newp = this->clone();
    if (this->m_op1p) newp->op1p(this->m_op1p->cloneTreeIterList());
    if (this->m_op2p) newp->op2p(this->m_op2p->cloneTreeIterList());
    if (this->m_op3p) newp->op3p(this->m_op3p->cloneTreeIterList());
    if (this->m_op4p) newp->op4p(this->m_op4p->cloneTreeIterList());
    newp->m_iterpp = nullptr;
    newp->clonep(this);  // Save pointers to/from both to simplify relinking.
    this->clonep(newp);  // Save pointers to/from both to simplify relinking.
    return newp;
}

AstNode* AstNode::cloneTreeIterList() {
    // private: Clone list of nodes, set m_headtailp
    AstNode* newheadp = nullptr;
    AstNode* newtailp = nullptr;
    // Audited to make sure this is never nullptr
    for (AstNode* oldp = this; oldp; oldp = oldp->m_nextp) {
        AstNode* const newp = oldp->cloneTreeIter();
        newp->m_headtailp = nullptr;
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
    debugTreeChange(this, "-cloneThs: ", __LINE__, cloneNextLink);
    cloneClearTree();
    AstNode* newp;
    if (cloneNextLink && this->m_nextp) {
        newp = cloneTreeIterList();
    } else {
        newp = cloneTreeIter();
        newp->m_nextp = nullptr;
        newp->m_headtailp = newp;
    }
    newp->m_backp = nullptr;
    newp->cloneRelinkTree();
    debugTreeChange(newp, "-cloneOut: ", __LINE__, true);
    return newp;
}

//======================================================================
// Delete

void AstNode::deleteNode() {
    // private: Delete single node. Publicly call deleteTree() instead.
    UASSERT(!m_backp, "Delete called on node with backlink still set");
    editCountInc();
    // Change links of old node so we coredump if used
    this->m_nextp = reinterpret_cast<AstNode*>(0x1);
    this->m_backp = reinterpret_cast<AstNode*>(0x1);
    this->m_headtailp = reinterpret_cast<AstNode*>(0x1);
    this->m_op1p = reinterpret_cast<AstNode*>(0x1);
    this->m_op2p = reinterpret_cast<AstNode*>(0x1);
    this->m_op3p = reinterpret_cast<AstNode*>(0x1);
    this->m_op4p = reinterpret_cast<AstNode*>(0x1);
    if (
#if !defined(VL_DEBUG) || defined(VL_LEAK_CHECKS)
        true
#else
        !v3Global.opt.debugLeak()
#endif
    ) {
        delete this;
    }
    // Else leak massively, so each pointer is unique
    // and we can debug easier.
}

void AstNode::deleteTreeIter() {
    // private: Delete list of nodes. Publicly call deleteTree() instead.
    // Audited to make sure this is never nullptr
    for (AstNode *nodep = this, *nnextp; nodep; nodep = nnextp) {
        nnextp = nodep->m_nextp;
        // MUST be depth first!
        if (nodep->m_op1p) nodep->m_op1p->deleteTreeIter();
        if (nodep->m_op2p) nodep->m_op2p->deleteTreeIter();
        if (nodep->m_op3p) nodep->m_op3p->deleteTreeIter();
        if (nodep->m_op4p) nodep->m_op4p->deleteTreeIter();
        nodep->m_nextp = nullptr;
        nodep->m_backp = nullptr;
        nodep->deleteNode();
    }
}

void AstNode::deleteTree() {
    // deleteTree always deletes the next link, because you must have called
    // unlinkFromBack or unlinkFromBackWithNext as appropriate before calling this.
    UASSERT(!m_backp, "Delete called on node with backlink still set");
    debugTreeChange(this, "-delTree:  ", __LINE__, true);
    this->editCountInc();
    // MUST be depth first!
    deleteTreeIter();
}

//======================================================================
// Memory checks

#ifdef VL_LEAK_CHECKS
void* AstNode::operator new(size_t size) {
    // Optimization note: Aligning to cache line is a loss, due to lost packing
    AstNode* const objp = static_cast<AstNode*>(::operator new(size));
    V3Broken::addNewed(objp);
    return objp;
}

void AstNode::operator delete(void* objp, size_t size) {
    if (!objp) return;
    const AstNode* const nodep = static_cast<AstNode*>(objp);
    V3Broken::deleted(nodep);
    ::operator delete(objp);
}
#endif

//======================================================================
// Iterators

void AstNode::iterateChildren(VNVisitor& v) {
    // This is a very hot function
    // Optimization note: Grabbing m_op#p->m_nextp is a net loss
    ASTNODE_PREFETCH(m_op1p);
    ASTNODE_PREFETCH(m_op2p);
    ASTNODE_PREFETCH(m_op3p);
    ASTNODE_PREFETCH(m_op4p);
    if (m_op1p) m_op1p->iterateAndNext(v);
    if (m_op2p) m_op2p->iterateAndNext(v);
    if (m_op3p) m_op3p->iterateAndNext(v);
    if (m_op4p) m_op4p->iterateAndNext(v);
}

void AstNode::iterateChildrenConst(VNVisitor& v) {
    // This is a very hot function
    ASTNODE_PREFETCH(m_op1p);
    ASTNODE_PREFETCH(m_op2p);
    ASTNODE_PREFETCH(m_op3p);
    ASTNODE_PREFETCH(m_op4p);
    if (m_op1p) m_op1p->iterateAndNextConst(v);
    if (m_op2p) m_op2p->iterateAndNextConst(v);
    if (m_op3p) m_op3p->iterateAndNextConst(v);
    if (m_op4p) m_op4p->iterateAndNextConst(v);
}

void AstNode::iterateAndNext(VNVisitor& v) {
    // This is a very hot function
    // IMPORTANT: If you replace a node that's the target of this iterator,
    // then the NEW node will be iterated on next, it isn't skipped!
    // Future versions of this function may require the node to have a back to be iterated;
    // there's no lower level reason yet though the back must exist.
    AstNode* nodep = this;
#ifdef VL_DEBUG  // Otherwise too hot of a function for debug
    UASSERT_OBJ(!(nodep && !nodep->m_backp), nodep, "iterateAndNext node has no back");
#endif
    if (nodep) ASTNODE_PREFETCH(nodep->m_nextp);
    while (nodep) {  // effectively: if (!this) return;  // Callers rely on this
        if (nodep->m_nextp) ASTNODE_PREFETCH(nodep->m_nextp->m_nextp);
        AstNode* niterp = nodep;  // Pointer may get stomped via m_iterpp if the node is edited
        // Desirable check, but many places where multiple iterations are OK
        // UASSERT_OBJ(!niterp->m_iterpp, niterp, "IterateAndNext under iterateAndNext may miss
        // edits"); Optimization note: Doing PREFETCH_RW on m_iterpp is a net even
        // cppcheck-suppress nullPointer
        niterp->m_iterpp = &niterp;
        niterp->accept(v);
        // accept may do a replaceNode and change niterp on us...
        // niterp maybe nullptr, so need cast if printing
        // if (niterp != nodep) UINFO(1,"iterateAndNext edited "<<cvtToHex(nodep)
        //                             <<" now into "<<cvtToHex(niterp)<<endl);
        if (!niterp) return;  // Perhaps node deleted inside accept
        niterp->m_iterpp = nullptr;
        if (VL_UNLIKELY(niterp != nodep)) {  // Edited node inside accept
            nodep = niterp;
        } else {  // Unchanged node, just continue loop
            nodep = niterp->m_nextp;
        }
    }
}

void AstNode::iterateListBackwards(VNVisitor& v) {
    AstNode* nodep = this;
    while (nodep->m_nextp) nodep = nodep->m_nextp;
    while (nodep) {
        // Edits not supported: nodep->m_iterpp = &nodep;
        nodep->accept(v);
        if (nodep->backp()->m_nextp == nodep) {
            nodep = nodep->backp();
        } else {
            nodep = nullptr;
        }  // else: backp points up the tree.
    }
}

void AstNode::iterateChildrenBackwards(VNVisitor& v) {
    if (m_op1p) m_op1p->iterateListBackwards(v);
    if (m_op2p) m_op2p->iterateListBackwards(v);
    if (m_op3p) m_op3p->iterateListBackwards(v);
    if (m_op4p) m_op4p->iterateListBackwards(v);
}

void AstNode::iterateAndNextConst(VNVisitor& v) {
    // Keep following the current list even if edits change it
    AstNode* nodep = this;
    do {
        AstNode* const nnextp = nodep->m_nextp;
        ASTNODE_PREFETCH(nnextp);
        nodep->accept(v);
        nodep = nnextp;
    } while (nodep);
}

AstNode* AstNode::iterateSubtreeReturnEdits(VNVisitor& v) {
    // Some visitors perform tree edits (such as V3Const), and may even
    // replace/delete the exact nodep that the visitor is called with.  If
    // this happens, the parent will lose the handle to the node that was
    // processed.
    // To solve this, this function returns the pointer to the replacement node,
    // which in many cases is just the same node that was passed in.
    AstNode* nodep = this;  // Note "this" may point to bogus point later in this function
    if (VN_IS(nodep, Netlist)) {
        // Calling on top level; we know the netlist won't get replaced
        nodep->accept(v);
    } else if (!nodep->backp()) {
        // Calling on standalone tree; insert a shim node so we can keep
        // track, then delete it on completion
        AstBegin* const tempp = new AstBegin(nodep->fileline(), "[EditWrapper]", nodep);
        {
            VL_DO_DANGLING(tempp->stmtsp()->accept(v),
                           nodep);  // nodep to null as may be replaced
        }
        nodep = tempp->stmtsp()->unlinkFrBackWithNext();
        VL_DO_DANGLING(tempp->deleteTree(), tempp);
    } else {
        // Use back to determine who's pointing at us (IE assume new node
        // grafts into same place as old one)
        AstNode** nextnodepp = nullptr;
        if (this->m_backp->m_op1p == this) {
            nextnodepp = &(this->m_backp->m_op1p);
        } else if (this->m_backp->m_op2p == this) {
            nextnodepp = &(this->m_backp->m_op2p);
        } else if (this->m_backp->m_op3p == this) {
            nextnodepp = &(this->m_backp->m_op3p);
        } else if (this->m_backp->m_op4p == this) {
            nextnodepp = &(this->m_backp->m_op4p);
        } else if (this->m_backp->m_nextp == this) {
            nextnodepp = &(this->m_backp->m_nextp);
        }
        UASSERT_OBJ(nextnodepp, this, "Node's back doesn't point to forward to node itself");
        {
            VL_DO_DANGLING(nodep->accept(v), nodep);  // nodep to null as may be replaced
        }
        nodep = *nextnodepp;  // Grab new node from point where old was connected
    }
    return nodep;
}

//======================================================================

void AstNode::cloneRelinkTree() {
    // private: Cleanup clone() operation on whole tree. Publicly call cloneTree() instead.
    for (AstNode* nodep = this; nodep; nodep = nodep->m_nextp) {
        if (nodep->m_dtypep && nodep->m_dtypep->clonep()) {
            nodep->m_dtypep = nodep->m_dtypep->clonep();
        }
        nodep->cloneRelink();
        if (nodep->m_op1p) nodep->m_op1p->cloneRelinkTree();
        if (nodep->m_op2p) nodep->m_op2p->cloneRelinkTree();
        if (nodep->m_op3p) nodep->m_op3p->cloneRelinkTree();
        if (nodep->m_op4p) nodep->m_op4p->cloneRelinkTree();
    }
}

//======================================================================
// Comparison

bool AstNode::gateTreeIter() const {
    // private: Return true if the two trees are identical
    if (!isGateOptimizable()) return false;
    if (m_op1p && !m_op1p->gateTreeIter()) return false;
    if (m_op2p && !m_op2p->gateTreeIter()) return false;
    if (m_op3p && !m_op3p->gateTreeIter()) return false;
    if (m_op4p && !m_op4p->gateTreeIter()) return false;
    return true;
}

bool AstNode::sameTreeIter(const AstNode* node1p, const AstNode* node2p, bool ignNext,
                           bool gateOnly) {
    // private: Return true if the two trees are identical
    if (!node1p && !node2p) return true;
    if (!node1p || !node2p) return false;
    if (node1p->type() != node2p->type() || node1p->dtypep() != node2p->dtypep()
        || !node1p->same(node2p) || (gateOnly && !node1p->isGateOptimizable())) {
        return false;
    }
    return (sameTreeIter(node1p->m_op1p, node2p->m_op1p, false, gateOnly)
            && sameTreeIter(node1p->m_op2p, node2p->m_op2p, false, gateOnly)
            && sameTreeIter(node1p->m_op3p, node2p->m_op3p, false, gateOnly)
            && sameTreeIter(node1p->m_op4p, node2p->m_op4p, false, gateOnly)
            && (ignNext || sameTreeIter(node1p->m_nextp, node2p->m_nextp, false, gateOnly)));
}

//======================================================================
// Debugging

void AstNode::checkTreeIter(AstNode* backp) {
    // private: Check a tree and children
    UASSERT_OBJ(backp == this->backp(), this, "Back node inconsistent");
    if (VN_IS(this, NodeTermop) || VN_IS(this, NodeVarRef)) {
        // Termops have a short-circuited iterateChildren, so check usage
        UASSERT_OBJ(!(op1p() || op2p() || op3p() || op4p()), this,
                    "Terminal operation with non-terminals");
    }
    if (m_op1p) m_op1p->checkTreeIterList(this);
    if (m_op2p) m_op2p->checkTreeIterList(this);
    if (m_op3p) m_op3p->checkTreeIterList(this);
    if (m_op4p) m_op4p->checkTreeIterList(this);
}

void AstNode::checkTreeIterList(AstNode* backp) {
    // private: Check a (possible) list of nodes, this is always the head of the list
    // Audited to make sure this is never nullptr
    AstNode* const headp = this;
    const AstNode* tailp = this;
    for (AstNode* nodep = headp; nodep; nodep = nodep->nextp()) {
        nodep->checkTreeIter(backp);
        UASSERT_OBJ(headp == this || !nextp(), this,
                    "Headtailp should be null in middle of lists");
        tailp = nodep;
        backp = nodep;
    }
    UASSERT_OBJ(headp->m_headtailp == tailp, headp, "Tail in headtailp is inconsistent");
    UASSERT_OBJ(tailp->m_headtailp == headp, tailp, "Head in headtailp is inconsistent");
}

void AstNode::checkTree() {
    if (!debug()) return;
    if (this->backp()) {
        // Linked tree- check only the passed node
        this->checkTreeIter(this->backp());
    } else {
        this->checkTreeIterList(this->backp());
    }
}

// cppcheck-suppress unusedFunction  // Debug only
void AstNode::dumpGdb(const AstNode* nodep) {  // For GDB only  // LCOV_EXCL_LINE
    if (!nodep) {
        cout << "<nullptr>" << endl;
        return;
    }
    nodep->dumpGdbHeader();
    cout << "  ";
    nodep->dump(cout);
    cout << endl;
}  // LCOV_EXCL_STOP
// cppcheck-suppress unusedFunction  // Debug only
void AstNode::dumpGdbHeader() const {  // For GDB only  // LCOV_EXCL_START
    dumpPtrs(cout);
    cout << "  Fileline = " << fileline() << endl;
}  // LCOV_EXCL_STOP
// cppcheck-suppress unusedFunction  // Debug only
void AstNode::dumpTreeGdb(const AstNode* nodep) {  // For GDB only  // LCOV_EXCL_START
    if (!nodep) {
        cout << "<nullptr>" << endl;
        return;
    }
    nodep->dumpGdbHeader();
    nodep->dumpTree(cout);
}  // LCOV_EXCL_STOP
// cppcheck-suppress unusedFunction  // Debug only
void AstNode::dumpTreeFileGdb(const AstNode* nodep,  // LCOV_EXCL_START
                              const char* filenamep) {  // For GDB only
    if (!nodep) {
        cout << "<nullptr>" << endl;
        return;
    }
    const string filename = filenamep ? filenamep : v3Global.debugFilename("debug.tree", 98);
    v3Global.rootp()->dumpTreeFile(filename);
}  // LCOV_EXCL_STOP

// cppcheck-suppress unusedFunction  // Debug only
void AstNode::checkIter() const {
    if (m_iterpp) {
        dumpPtrs(cout);
        // Perhaps something forgot to clear m_iterpp?
        this->v3fatalSrc("Iteration link should be nullptr");
    }
}

void AstNode::dumpPtrs(std::ostream& os) const {
    os << "This=" << typeName() << " " << cvtToHex(this);
    os << " back=" << cvtToHex(backp());
    if (nextp()) os << " next=" << cvtToHex(nextp());
    if (m_headtailp == this) {
        os << " headtail=this";
    } else {
        os << " headtail=" << cvtToHex(m_headtailp);
    }
    if (op1p()) os << " op1p=" << cvtToHex(op1p());
    if (op2p()) os << " op2p=" << cvtToHex(op2p());
    if (op3p()) os << " op3p=" << cvtToHex(op3p());
    if (op4p()) os << " op4p=" << cvtToHex(op4p());
    if (user1p()) os << " user1p=" << cvtToHex(user1p());
    if (user2p()) os << " user2p=" << cvtToHex(user2p());
    if (user3p()) os << " user3p=" << cvtToHex(user3p());
    if (user4p()) os << " user4p=" << cvtToHex(user4p());
    if (user5p()) os << " user5p=" << cvtToHex(user5p());
    if (m_iterpp) {
        os << " iterpp=" << cvtToHex(m_iterpp);
        os << "*=" << cvtToHex(*m_iterpp);
    }
    os << endl;
}

void AstNode::dumpTree(std::ostream& os, const string& indent, int maxDepth) const {
    static int s_debugFileline = v3Global.opt.debugSrcLevel("fileline");  // --debugi-fileline 9
    os << indent << " " << this << '\n';
    if (debug() > 8) {
        os << indent << "     ";
        dumpPtrs(os);
    }
    if (s_debugFileline >= 9) os << fileline()->warnContextSecondary();
    if (maxDepth == 1) {
        if (op1p() || op2p() || op3p() || op4p()) os << indent << "1: ...(maxDepth)\n";
    } else {
        for (const AstNode* nodep = op1p(); nodep; nodep = nodep->nextp()) {
            nodep->dumpTree(os, indent + "1:", maxDepth - 1);
        }
        for (const AstNode* nodep = op2p(); nodep; nodep = nodep->nextp()) {
            nodep->dumpTree(os, indent + "2:", maxDepth - 1);
        }
        for (const AstNode* nodep = op3p(); nodep; nodep = nodep->nextp()) {
            nodep->dumpTree(os, indent + "3:", maxDepth - 1);
        }
        for (const AstNode* nodep = op4p(); nodep; nodep = nodep->nextp()) {
            nodep->dumpTree(os, indent + "4:", maxDepth - 1);
        }
    }
}

void AstNode::dumpTreeAndNext(std::ostream& os, const string& indent, int maxDepth) const {
    // Audited to make sure this is never nullptr
    for (const AstNode* nodep = this; nodep; nodep = nodep->nextp()) {
        nodep->dumpTree(os, indent, maxDepth);
    }
}

void AstNode::dumpTreeFile(const string& filename, bool append, bool doDump, bool doCheck) {
    // Not const function as calls checkTree
    if (doDump) {
        {  // Write log & close
            UINFO(2, "Dumping " << filename << endl);
            const std::unique_ptr<std::ofstream> logsp{V3File::new_ofstream(filename, append)};
            if (logsp->fail()) v3fatal("Can't write " << filename);
            *logsp << "Verilator Tree Dump (format 0x3900) from <e" << std::dec << editCountLast();
            *logsp << "> to <e" << std::dec << editCountGbl() << ">\n";
            if (editCountGbl() == editCountLast() && !(v3Global.opt.dumpTree() >= 9)) {
                *logsp << '\n';
                *logsp << "No changes since last dump!\n";
            } else {
                dumpTree(*logsp);
                editCountSetLast();  // Next dump can indicate start from here
            }
        }
    }
    if (doDump && v3Global.opt.debugEmitV()) V3EmitV::debugEmitV(filename + ".v");
    if (doCheck && (v3Global.opt.debugCheck() || v3Global.opt.dumpTree())) {
        // Error check
        checkTree();
        // Broken isn't part of check tree because it can munge iterp's
        // set by other steps if it is called in the middle of other operations
        if (AstNetlist* const netp = VN_CAST(this, Netlist)) V3Broken::brokenAll(netp);
    }
}

void AstNode::v3errorEndFatal(std::ostringstream& str) const {
    v3errorEnd(str);
    assert(0);  // LCOV_EXCL_LINE
    VL_UNREACHABLE
}

string AstNode::instanceStr() const {
    // Max iterations before giving up on location search,
    // in case we have some circular reference bug.
    constexpr unsigned maxIterations = 10000;
    unsigned iterCount = 0;

    for (const AstNode* backp = this; backp; backp = backp->backp(), ++iterCount) {
        if (VL_UNCOVERABLE(iterCount >= maxIterations)) return "";  // LCOV_EXCL_LINE

        // Prefer the enclosing scope, if there is one. This is always under the enclosing module,
        // so just pick it up when encountered
        if (const AstScope* const scopep = VN_CAST(backp, Scope)) {
            return scopep->isTop() ? "" : "... In instance " + scopep->prettyName();
        }

        // If scopes don't exist, report an example instance of the enclosing module
        if (const AstModule* const modp = VN_CAST(backp, Module)) {
            const string instanceName = modp->someInstanceName();
            return instanceName.empty() ? "" : "... In instance " + instanceName;
        }
    }

    return "";
}
void AstNode::v3errorEnd(std::ostringstream& str) const {
    if (!m_fileline) {
        V3Error::v3errorEnd(str, instanceStr());
    } else {
        std::ostringstream nsstr;
        nsstr << str.str();
        if (debug()) {
            nsstr << '\n';
            nsstr << "-node: ";
            const_cast<AstNode*>(this)->dump(nsstr);
            nsstr << endl;
        }
        m_fileline->v3errorEnd(nsstr, instanceStr());
    }
}

//======================================================================
// Data type conversion

void AstNode::dtypeChgSigned(bool flag) {
    UASSERT_OBJ(dtypep(), this, "No dtype when changing to (un)signed");
    dtypeChgWidthSigned(dtypep()->width(), dtypep()->widthMin(), VSigning::fromBool(flag));
}
void AstNode::dtypeChgWidth(int width, int widthMin) {
    UASSERT_OBJ(dtypep(), this,
                "No dtype when changing width");  // Use ChgWidthSigned(...UNSIGNED) otherwise
    dtypeChgWidthSigned(width, widthMin, dtypep()->numeric());
}

void AstNode::dtypeChgWidthSigned(int width, int widthMin, VSigning numeric) {
    if (!dtypep()) {
        // We allow dtypep() to be null, as before/during widthing dtypes are not resolved
        dtypeSetLogicUnsized(width, widthMin, numeric);
    } else {
        if (width == dtypep()->width() && widthMin == dtypep()->widthMin()
            && numeric == dtypep()->numeric())
            return;  // Correct already
        // FUTURE: We may be pointing at a two state data type, and this may
        // convert it to logic.  Since the AstVar remains correct, we
        // work OK but this assumption may break in the future.
        // Note we can't just clone and do a widthForce, as if it's a BasicDType
        // the msb() indications etc will be incorrect.
        dtypeSetLogicUnsized(width, widthMin, numeric);
    }
}

AstNodeDType* AstNode::findBasicDType(VBasicDTypeKwd kwd) const {
    // For 'simple' types we use the global directory.  These are all unsized.
    // More advanced types land under the module/task/etc
    return v3Global.rootp()->typeTablep()->findBasicDType(fileline(), kwd);
}
AstNodeDType* AstNode::findBitDType(int width, int widthMin, VSigning numeric) const {
    return v3Global.rootp()->typeTablep()->findLogicBitDType(fileline(), VBasicDTypeKwd::BIT,
                                                             width, widthMin, numeric);
}
AstNodeDType* AstNode::findLogicDType(int width, int widthMin, VSigning numeric) const {
    return v3Global.rootp()->typeTablep()->findLogicBitDType(fileline(), VBasicDTypeKwd::LOGIC,
                                                             width, widthMin, numeric);
}
AstNodeDType* AstNode::findLogicRangeDType(const VNumRange& range, int widthMin,
                                           VSigning numeric) const {
    return v3Global.rootp()->typeTablep()->findLogicBitDType(fileline(), VBasicDTypeKwd::LOGIC,
                                                             range, widthMin, numeric);
}
AstNodeDType* AstNode::findBitRangeDType(const VNumRange& range, int widthMin,
                                         VSigning numeric) const {
    return v3Global.rootp()->typeTablep()->findLogicBitDType(fileline(), VBasicDTypeKwd::BIT,
                                                             range, widthMin, numeric);
}
AstBasicDType* AstNode::findInsertSameDType(AstBasicDType* nodep) {
    return v3Global.rootp()->typeTablep()->findInsertSameDType(nodep);
}
AstNodeDType* AstNode::findEmptyQueueDType() const {
    return v3Global.rootp()->typeTablep()->findEmptyQueueDType(fileline());
}
AstNodeDType* AstNode::findQueueIndexDType() const {
    return v3Global.rootp()->typeTablep()->findQueueIndexDType(fileline());
}
AstNodeDType* AstNode::findVoidDType() const {
    return v3Global.rootp()->typeTablep()->findVoidDType(fileline());
}

//######################################################################
// VNDeleter

void VNDeleter::doDeletes() {
    for (AstNode* const nodep : m_deleteps) nodep->deleteTree();
    m_deleteps.clear();
}

//######################################################################
// VNVisitor

#include "V3Ast__gen_visitor_defns.h"  // From ./astgen
