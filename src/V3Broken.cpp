// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Find broken links in tree
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
// V3Broken's Transformations:
//
// Entire netlist
//      Mark all nodes
//      Check all links point to marked nodes
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Broken.h"
#include "V3Ast.h"

// This visitor does not edit nodes, and is called at error-exit, so should use constant iterators
#include "V3AstConstOnly.h"

#include <algorithm>
#include <cstdarg>
#include VL_INCLUDE_UNORDERED_MAP

//######################################################################

class BrokenTable : public AstNVisitor {
    // Table of brokenExists node pointers
private:
    // MEMBERS
    //   For each node, we keep if it exists or not.
    typedef vl_unordered_map<const AstNode*,int> NodeMap;  // Performance matters (when --debug)
    static NodeMap s_nodes;  // Set of all nodes that exist
    // BITMASK
    enum { FLAG_ALLOCATED       = 0x01 };  // new() and not delete()ed
    enum { FLAG_IN_TREE         = 0x02 };  // Is in netlist tree
    enum { FLAG_LINKABLE        = 0x04 };  // Is in netlist tree, can be linked to
    enum { FLAG_LEAKED          = 0x08 };  // Known to have been leaked
    enum { FLAG_UNDER_NOW       = 0x10 };  // Is in tree as parent of current node
public:
    // METHODS
    static void deleted(const AstNode* nodep) {
        // Called by operator delete on any node - only if VL_LEAK_CHECKS
        if (debug()>=9) cout<<"-nodeDel:  "<<cvtToHex(nodep)<<endl;
        NodeMap::iterator iter = s_nodes.find(nodep);
        UASSERT_OBJ(!(iter==s_nodes.end() || !(iter->second & FLAG_ALLOCATED)),
                    reinterpret_cast<const AstNode*>(nodep),
                    "Deleting AstNode object that was never tracked or already deleted");
        if (iter!=s_nodes.end()) s_nodes.erase(iter);
    }
#if defined(__GNUC__) && __GNUC__ == 4 && __GNUC_MINOR__ == 4
    // GCC 4.4.* compiler warning bug, https://gcc.gnu.org/bugzilla/show_bug.cgi?id=39390
# pragma GCC diagnostic ignored "-Wstrict-aliasing"
#endif
    static void addNewed(const AstNode* nodep) {
        // Called by operator new on any node - only if VL_LEAK_CHECKS
        if (debug()>=9) cout<<"-nodeNew:  "<<cvtToHex(nodep)<<endl;
        NodeMap::iterator iter = s_nodes.find(nodep);
        UASSERT_OBJ(!(iter !=s_nodes.end() && (iter->second & FLAG_ALLOCATED)),
                    nodep, "Newing AstNode object that is already allocated");
        if (iter == s_nodes.end()) {
            int flags = FLAG_ALLOCATED;  // This int needed to appease GCC 4.1.2
            s_nodes.insert(make_pair(nodep, flags));
        }
    }
    static void setUnder(const AstNode* nodep, bool flag) {
        // Called by BrokenCheckVisitor when each node entered/exited
        if (!okIfLinkedTo(nodep)) return;
        NodeMap::iterator iter = s_nodes.find(nodep);
        if (iter!=s_nodes.end()) {
            iter->second &= ~FLAG_UNDER_NOW;
            if (flag) iter->second |=  FLAG_UNDER_NOW;
        }
    }
    static void addInTree(AstNode* nodep, bool linkable) {
#ifndef VL_LEAK_CHECKS
        if (!linkable) return;  // save some time, else the map will get huge!
#endif
        NodeMap::iterator iter = s_nodes.find(nodep);
        if (VL_UNCOVERABLE(iter == s_nodes.end())) {
#ifdef VL_LEAK_CHECKS
            nodep->v3fatalSrc("AstNode is in tree, but not allocated");
#endif
        } else {
#ifdef VL_LEAK_CHECKS
            UASSERT_OBJ(iter->second & FLAG_ALLOCATED, nodep,
                        "AstNode is in tree, but not allocated");
#endif
            UASSERT_OBJ(!(iter->second & FLAG_IN_TREE), nodep,
                        "AstNode is already in tree at another location");
        }
        int or_flags = FLAG_IN_TREE | (linkable?FLAG_LINKABLE:0);
        if (iter == s_nodes.end()) {
            s_nodes.insert(make_pair(nodep, or_flags));
        } else {
            iter->second |= or_flags;
        }
    }
    static bool isAllocated(const AstNode* nodep) {
        // Some generic node has a pointer to this node.  Is it allocated?
        // Use this when might not be in tree; otherwise use okIfLinkedTo().
#ifdef VL_LEAK_CHECKS
        NodeMap::iterator iter = s_nodes.find(nodep);
        if (iter == s_nodes.end()) return false;
        if (!(iter->second & FLAG_ALLOCATED)) return false;
#endif
        return true;
    }
    static bool okIfLinkedTo(const AstNode* nodep) {
        // Some node in tree has a pointer to this node.  Is it kosher?
        NodeMap::iterator iter = s_nodes.find(nodep);
        if (iter == s_nodes.end()) return false;
#ifdef VL_LEAK_CHECKS
        if (!(iter->second & FLAG_ALLOCATED)) return false;
#endif
        if (!(iter->second & FLAG_IN_TREE)) return false;
        if (!(iter->second & FLAG_LINKABLE)) return false;
        return true;
    }
    static bool okIfBelow(const AstNode* nodep) {
        // Must be linked to and below current node
        if (!okIfLinkedTo(nodep)) return false;
        NodeMap::iterator iter = s_nodes.find(nodep);
        if (iter == s_nodes.end()) return false;
        if (!(iter->second & FLAG_UNDER_NOW)) return false;
        return true;
    }
    static void prepForTree() {
#ifndef VL_LEAK_CHECKS
        s_nodes.clear();
#endif
        for (NodeMap::iterator it = s_nodes.begin(); it != s_nodes.end(); ++it) {
            it->second &= ~FLAG_IN_TREE;
            it->second &= ~FLAG_LINKABLE;
        }
    }
    static void doneWithTree() {
        for (int backs=0; backs<2; backs++) {  // Those with backp() are probably under one leaking without
            for (NodeMap::iterator it = s_nodes.begin(); it != s_nodes.end(); ++it) {
                if ((it->second & FLAG_ALLOCATED)
                    && !(it->second & FLAG_IN_TREE)
                    && !(it->second & FLAG_LEAKED)
                    && (it->first->backp() ? backs==1 : backs==0)) {
                    // Use only AstNode::dump instead of the virtual one, as there
                    // may be varp() and other cross links that are bad.
                    if (v3Global.opt.debugCheck()) {
                        // When get this message, find what forgot to delete the
                        // node by running GDB, where for node "<e###>" use:
                        //    watch AstNode::s_editCntGbl==####
                        //    run
                        //    bt
                        std::cerr<<"%Error: LeakedNode"<<(it->first->backp()?"Back: ":": ");
                        AstNode* rawp = const_cast<AstNode*>
                            (static_cast<const AstNode*>(it->first));
                        rawp->AstNode::dump(std::cerr);
                        std::cerr<<endl;
                        V3Error::incErrors();
                    }
                    it->second |= FLAG_LEAKED;
                }
            }
        }
    }
public:
    // CONSTRUCTORS
    BrokenTable() {}
    virtual ~BrokenTable() {}
};

BrokenTable::NodeMap BrokenTable::s_nodes;

bool AstNode::brokeExists() const {
    // Called by node->broken() routines to do table lookup
    return BrokenTable::okIfLinkedTo(this);
}
bool AstNode::brokeExistsAbove() const {
    // Called by node->broken() routines to do table lookup
    return BrokenTable::okIfBelow(this);
}

//######################################################################

class BrokenMarkVisitor : public AstNVisitor {
    // Mark every node in the tree
private:
    // NODE STATE
    //  Nothing!        // This may be called deep inside other routines
    //                  // so userp and friends may not be used
    // METHODS
    void processAndIterate(AstNode* nodep) {
        BrokenTable::addInTree(nodep, nodep->maybePointedTo());
        iterateChildrenConst(nodep);
    }
    // VISITORS
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        processAndIterate(nodep);
    }
public:
    // CONSTRUCTORS
    explicit BrokenMarkVisitor(AstNetlist* nodep) {
        iterate(nodep);
    }
    virtual ~BrokenMarkVisitor() {}
};

//######################################################################
// Broken state, as a visitor of each AstNode

class BrokenCheckVisitor : public AstNVisitor {
private:
    void checkWidthMin(const AstNode* nodep) {
        UASSERT_OBJ(nodep->width() == nodep->widthMin()
                    || v3Global.widthMinUsage() != VWidthMinUsage::MATCHES_WIDTH,
                    nodep, "Width != WidthMin");
    }
    void processAndIterate(AstNode* nodep) {
        BrokenTable::setUnder(nodep, true);
        const char* whyp = nodep->broken();
        UASSERT_OBJ(!whyp, nodep,
                    "Broken link in node (or something without maybePointedTo): "<<whyp);
        if (nodep->dtypep()) {
            UASSERT_OBJ(nodep->dtypep()->brokeExists(), nodep,
                        "Broken link in node->dtypep() to "<<cvtToHex(nodep->dtypep()));
            UASSERT_OBJ(VN_IS(nodep->dtypep(), NodeDType), nodep,
                        "Non-dtype link in node->dtypep() to "<<cvtToHex(nodep->dtypep()));
        }
        if (v3Global.assertDTypesResolved()) {
            if (nodep->hasDType()) {
                UASSERT_OBJ(nodep->dtypep(), nodep,
                            "No dtype on node with hasDType(): "<<nodep->prettyTypeName());
            } else {
                UASSERT_OBJ(!nodep->dtypep(), nodep,
                            "DType on node without hasDType(): "<<nodep->prettyTypeName());
            }
            UASSERT_OBJ(!nodep->getChildDTypep(), nodep,
                        "childDTypep() non-null on node after should have removed");
            if (const AstNodeDType* dnodep = VN_CAST(nodep, NodeDType)) checkWidthMin(dnodep);
        }
        checkWidthMin(nodep);
        iterateChildrenConst(nodep);
        BrokenTable::setUnder(nodep, false);
    }
    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        processAndIterate(nodep);
        UASSERT_OBJ(!(v3Global.assertDTypesResolved()
                      && nodep->brokeLhsMustBeLvalue()
                      && VN_IS(nodep->lhsp(), NodeVarRef)
                      && !VN_CAST(nodep->lhsp(), NodeVarRef)->lvalue()),
                    nodep, "Assignment LHS is not an lvalue");
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        processAndIterate(nodep);
    }
public:
    // CONSTRUCTORS
    explicit BrokenCheckVisitor(AstNetlist* nodep) {
        iterate(nodep);
    }
    virtual ~BrokenCheckVisitor() {}
};

//######################################################################
// Broken class functions

void V3Broken::brokenAll(AstNetlist* nodep) {
    //UINFO(9,__FUNCTION__<<": "<<endl);
    static bool inBroken = false;
    if (VL_UNCOVERABLE(inBroken)) {
        // A error called by broken can recurse back into broken; avoid this
        UINFO(1,"Broken called under broken, skipping recursion.\n");  // LCOV_EXCL_LINE
    } else {
        inBroken = true;
        BrokenTable::prepForTree();
        BrokenMarkVisitor mvisitor (nodep);
        BrokenCheckVisitor cvisitor (nodep);
        BrokenTable::doneWithTree();
        inBroken = false;
    }
}

void V3Broken::addNewed(AstNode* nodep) {
    BrokenTable::addNewed(nodep);
}
void V3Broken::deleted(AstNode* nodep) {
    BrokenTable::deleted(nodep);
}
bool V3Broken::isAllocated(AstNode* nodep) {
    return BrokenTable::isAllocated(nodep);
}
