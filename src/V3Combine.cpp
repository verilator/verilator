// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Combine common code into functions
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
// V3Combine's Transformations:
//
//      For every function that we spit out
//      Examine code to find largest common blocks
//          Hash each node depth first
//              Hash includes varp name and operator type, and constants
//              Form lookup table based on hash of each statement  w/ nodep and next nodep
//          GO through table
//              Lookup in hash, while next of each statement match, grow that common block
//      Foreach common block
//          If common block large enough (> 20 statements) & used 2x or more
//              Make new function
//              Move common block to function
//              Replace each common block ref with funccall
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Combine.h"
#include "V3Hashed.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <algorithm>
#include <map>
#include <vector>

//######################################################################

#ifdef VL_COMBINE_STATEMENTS
constexpr int COMBINE_MIN_STATEMENTS = 50;  // Min # of statements to be worth making a function
#endif

//######################################################################

class CombBaseVisitor VL_NOT_FINAL : public AstNVisitor {
protected:
    // STATE

    // METHODS
    virtual ~CombBaseVisitor() override = default;
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Combine replacement function

class CombCallVisitor final : CombBaseVisitor {
    // Find all CCALLS of each CFUNC, so that we can later rename them
private:
    // NODE STATE
    typedef std::multimap<AstCFunc*, AstCCall*> CallMmap;
    CallMmap m_callMmap;  // Associative array of {function}{call}
    // METHODS
public:
    void replaceFunc(AstCFunc* oldfuncp, AstCFunc* newfuncp) {
        if (oldfuncp == newfuncp) return;
        if (newfuncp) {
            UINFO(4, "   Replace " << oldfuncp << " -WITH-> " << newfuncp << endl);
        } else {
            UINFO(4, "   Remove " << oldfuncp << endl);
        }
        // Note: m_callMmap modified in loop, so not using equal_range.
        for (CallMmap::iterator it = m_callMmap.find(oldfuncp); it != m_callMmap.end();
             it = m_callMmap.find(oldfuncp)) {
            AstCCall* callp = it->second;
            if (!callp->user3()) {  // !already done
                UINFO(4, "     Called " << callp << endl);
                UASSERT_OBJ(callp->funcp() == oldfuncp, callp,
                            "Call list broken, points to call w/different func");
                if (newfuncp) {
                    AstCCall* newp = new AstCCall(callp, newfuncp);
                    // Special new AstCCall form above transfers children of callp to newfuncp
                    callp->replaceWith(newp);
                    addCall(newp);  // Fix the table
                } else {  // Just deleting empty function
                    callp->unlinkFrBack();
                }
                callp->user3(true);  // Dead now
                VL_DO_DANGLING(pushDeletep(callp), callp);
            }
            // It is safe to unconditionally remove this entry here as the above
            // 'if' would never be entered again for this entry (we set user3).
            // The only other place where m_callMmap is looked up is deleteCall
            // below, but that is only ever called straight after an addCall
            // of the node being deleted, so it won't miss this entry.
            m_callMmap.erase(it);  // Fix the table
        }
    }
    // METHODS
    void addCall(AstCCall* nodep) { m_callMmap.insert(make_pair(nodep->funcp(), nodep)); }
    void deleteCall(AstCCall* nodep) {
        std::pair<CallMmap::iterator, CallMmap::iterator> eqrange
            = m_callMmap.equal_range(nodep->funcp());
        for (auto nextit = eqrange.first; nextit != eqrange.second;) {
            const auto eqit = nextit++;
            AstCCall* callp = eqit->second;
            if (callp == nodep) {
                m_callMmap.erase(eqit);
                return;
            }
        }
        nodep->v3fatalSrc("deleteCall node not found in table");
    }

private:
    // VISITORS
    virtual void visit(AstCCall* nodep) override { addCall(nodep); }
    // Speed things up
    virtual void visit(AstNodeAssign*) override {}
    virtual void visit(AstNodeMath*) override {}
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    CombCallVisitor() = default;
    virtual ~CombCallVisitor() override = default;
    void main(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// Combine marking function

class CombMarkVisitor final : CombBaseVisitor {
    // Mark all nodes under specified one.
private:
    // OUTPUT:
    //  AstNode::user3()        -> bool. True to indicate duplicated
    // VISITORS
    virtual void visit(AstNode* nodep) override {
        nodep->user3(true);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CombMarkVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~CombMarkVisitor() override = default;
};

//######################################################################
// Combine state, as a visitor of each AstNode

class CombineVisitor final : CombBaseVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNodeStmt::user()     -> bool.  True if iterated already
    //  AstCFunc::user3p()      -> AstCFunc*, If set, replace ccalls to this func with new func
    //  AstNodeStmt::user3()    -> AstNode*.  True if to ignore this cell
    //  AstNodeStmt::user4()    -> V3Hashed::V3Hash.  Hash value of this node (hash of 0 is
    //  illegal)
    AstUser1InUse m_inuser1;
    AstUser3InUse m_inuser3;
    // AstUser4InUse     part of V3Hashed

    // STATE
    typedef enum : uint8_t { STATE_IDLE, STATE_HASH, STATE_DUP } CombineState;
    VDouble0 m_statCombs;  // Statistic tracking
    CombineState m_state = STATE_IDLE;  // Major state
    AstNodeModule* m_modp = nullptr;  // Current module
    AstCFunc* m_cfuncp = nullptr;  // Current function
    CombCallVisitor m_call;  // Tracking of function call users
    int m_modNFuncs = 0;  // Number of functions made
#ifdef VL_COMBINE_STATEMENTS
    AstNode* m_walkLast1p = nullptr;  // Final node that is the same in duplicate list
#endif
    AstNode* m_walkLast2p = nullptr;  // Final node that is the same in duplicate list
    V3Hashed m_hashed;  // Hash for every node in module

    // METHODS
    void hashStatement(AstNode* nodep) {
        // Compute hash on entire tree of this statement
        m_hashed.hashAndInsert(nodep);
        // UINFO(9, "  stmthash " << hex << nodep->user4() << "  " << nodep << endl);
    }
#ifdef VL_COMBINE_STATEMENTS
    void hashFunctions(AstCFunc* nodep) {
        // Compute hash of all statement trees in the function
        VL_RESTORER(m_state);
        {
            m_state = STATE_HASH;
            iterate(nodep);
        }
    }
#endif
    void walkEmptyFuncs() {
        for (const auto& itr : m_hashed) {
            AstNode* node1p = itr.second;
            AstCFunc* oldfuncp = VN_CAST(node1p, CFunc);
            if (oldfuncp && oldfuncp->emptyBody() && !oldfuncp->dontCombine()) {
                UINFO(5, "     EmptyFunc " << std::hex << V3Hash(oldfuncp->user4p()) << " "
                                           << oldfuncp << endl);
                // Mark user3p on entire old tree, so we don't process it more
                CombMarkVisitor visitor(oldfuncp);
                m_call.replaceFunc(oldfuncp, nullptr);
                oldfuncp->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(oldfuncp), oldfuncp);
            }
        }
    }
    void walkDupFuncs() {
        // Do non-slow first as then favors naming functions based on fast name
        for (int slow = 0; slow < 2; ++slow) {
            for (V3Hashed::iterator it = m_hashed.begin(); it != m_hashed.end(); ++it) {
                AstNode* node1p = it->second;
                AstCFunc* cfunc1p = VN_CAST(node1p, CFunc);
                if (!cfunc1p) continue;
                if (cfunc1p->slow() != slow) continue;
                V3Hash hashval = it->first;
                UASSERT_OBJ(!hashval.isIllegal(), node1p, "Illegal (unhashed) nodes");
                for (V3Hashed::iterator eqit = it; eqit != m_hashed.end(); ++eqit) {
                    AstNode* node2p = eqit->second;
                    if (!(eqit->first == hashval)) break;
                    if (node1p == node2p) continue;  // Identical iterator
                    if (node1p->user3p() || node2p->user3p()) continue;  // Already merged
                    if (node1p->sameTree(node2p)) {  // walk of tree has same comparison
                        // Replace AstCCall's that point here
                        replaceFuncWFunc(VN_CAST(node2p, CFunc), cfunc1p);
                        // Replacement may promote a slow routine to fast path
                        if (!VN_CAST(node2p, CFunc)->slow()) cfunc1p->slow(false);
                    }
                }
            }
        }
    }
    void replaceFuncWFunc(AstCFunc* oldfuncp, AstCFunc* newfuncp) {
        UINFO(5, "     DupFunc " << std::hex << V3Hash(newfuncp->user4p()) << " " << newfuncp
                                 << endl);
        UINFO(5, "         and " << std::hex << V3Hash(oldfuncp->user4p()) << " " << oldfuncp
                                 << endl);
        // Mark user3p on entire old tree, so we don't process it more
        ++m_statCombs;
        CombMarkVisitor visitor(oldfuncp);
        m_call.replaceFunc(oldfuncp, newfuncp);
        oldfuncp->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(oldfuncp), oldfuncp);
    }

#ifdef VL_COMBINE_STATEMENTS
    void replaceOnlyCallFunc(AstCCall* nodep) {
        if (AstCFunc* oldfuncp = VN_CAST(nodep->backp(), CFunc)) {
            // oldfuncp->dumpTree(cout, "MAYDEL: ");
            if (nodep->nextp() == nullptr && oldfuncp->initsp() == nullptr
                && oldfuncp->stmtsp() == nodep && oldfuncp->finalsp() == nullptr) {
                UINFO(9, "     Function only has call " << oldfuncp << endl);
                m_call.deleteCall(nodep);
                CombMarkVisitor visitor(oldfuncp);
                VL_DO_DANGLING(replaceFuncWFunc(oldfuncp, nodep->funcp()), nodep);
            }
        }
    }

    void walkDupCodeStart(AstNode* node1p) {
        V3Hash hashval(node1p->user4p());
        // UINFO(4,"    STMT " << hashval << " " << node1p << endl);
        //
        int bestDepth = 0;  // Best substitution found in the search
        AstNode* bestNode2p = nullptr;
        AstNode* bestLast1p = nullptr;
        AstNode* bestLast2p = nullptr;
        //
        std::pair<V3Hashed::iterator, V3Hashed::iterator> eqrange
            = m_hashed.mmap().equal_range(hashval);
        for (V3Hashed::iterator eqit = eqrange.first; eqit != eqrange.second; ++eqit) {
            AstNode* node2p = eqit->second;
            if (node1p == node2p) continue;
            //
            // We need to mark iteration to prevent matching code inside
            // code (abab matching in ababab)
            AstNode::user1ClearTree();  // user1p() used on entire tree
            m_walkLast1p = nullptr;
            m_walkLast2p = nullptr;
            int depth = walkDupCodeNext(node1p, node2p, 1);
            if (depth > COMBINE_MIN_STATEMENTS && depth > bestDepth) {
                bestDepth = depth;
                bestNode2p = node2p;
                bestLast1p = m_walkLast1p;
                bestLast2p = m_walkLast2p;
            }
        }
        if (bestDepth) {
            // Found a replacement
            UINFO(5, "     Duplicate of depth " << bestDepth << endl);
            UINFO(5, "       DupFunc "
                         << " " << node1p << endl);
            UINFO(5, "           and "
                         << " " << bestNode2p << endl);
            UINFO(5, "       Through "
                         << " " << bestLast1p << endl);
            UINFO(5, "           and "
                         << " " << bestLast2p << endl);
            //
            walkReplace(node1p, bestNode2p, bestLast1p, bestLast2p);
        }
    }

    int walkDupCodeNext(AstNode* node1p, AstNode* node2p, int level) {
        // Find number of common statements between the two node1p_nextp's...
        if (node1p->user1p() || node2p->user1p()) return 0;  // Already iterated
        if (node1p->user3p() || node2p->user3p()) return 0;  // Already merged
        if (!m_hashed.sameNodes(node1p, node2p)) return 0;  // walk of tree has same comparison
        V3Hash hashval(node1p->user4p());
        // UINFO(9, "        wdup1 "<<level<<" "<<V3Hash(node1p->user4p())<<" "<<node1p<<endl);
        // UINFO(9, "        wdup2 "<<level<<" "<<V3Hash(node2p->user4p())<<" "<<node2p<<endl);
        m_walkLast1p = node1p;
        m_walkLast2p = node2p;
        node1p->user1(true);
        node2p->user1(true);
        if (node1p->nextp() && node2p->nextp()) {
            return hashval.depth() + walkDupCodeNext(node1p->nextp(), node2p->nextp(), level + 1);
        }
        return hashval.depth();
    }

    void walkReplace(AstNode* node1p, AstNode* node2p, AstNode* last1p,
                     AstNode* last2p) {  // Final node in linked list, maybe null if all statements
                                         // to be grabbed
        // Make new function
        string oldname = m_cfuncp->name();
        string::size_type pos;
        if ((pos = oldname.find("_common")) != string::npos) oldname.erase(pos);
        if ((pos = oldname.find("__")) != string::npos) oldname.erase(pos);
        AstCFunc* newfuncp = new AstCFunc(node1p->fileline(),
                                          oldname + "_common" + cvtToStr(++m_modNFuncs), nullptr);
        m_modp->addStmtp(newfuncp);
        // Create calls
        AstCCall* call1p = new AstCCall(node1p->fileline(), newfuncp);
        AstCCall* call2p = new AstCCall(node2p->fileline(), newfuncp);
        // Grab statement bodies
        AstNRelinker relink1Handle;
        AstNRelinker relink2Handle;
        for (AstNode *nextp, *walkp = node1p; true; walkp = nextp) {
            nextp = walkp->nextp();
            if (walkp == node1p) {
                walkp->unlinkFrBack(&relink1Handle);
            } else {
                walkp->unlinkFrBack();
                node1p->addNext(walkp);
            }
            if (walkp == last1p) break;
        }
        for (AstNode *nextp, *walkp = node2p; true; walkp = nextp) {
            nextp = walkp->nextp();
            if (walkp == node2p) {
                walkp->unlinkFrBack(&relink2Handle);
            } else {
                walkp->unlinkFrBack();
                node2p->addNext(walkp);
            }
            if (walkp == last2p) break;
        }
        // Move node1 statements to new function
        newfuncp->addStmtsp(node1p);
        // newfuncp->dumpTree(cout, " newfunctree: ");
        // Mark node2 statements as dead
        CombMarkVisitor visitor(node2p);
        pushDeletep(node2p);  // Delete later
        // Link in new function
        relink1Handle.relink(call1p);
        relink2Handle.relink(call2p);
        // Hash the new function
        hashFunctions(newfuncp);
        m_call.addCall(call1p);
        m_call.addCall(call2p);
        // If either new statement makes a func with only a single call, replace
        // the above callers to call it directly
        VL_DO_DANGLING(replaceOnlyCallFunc(call1p), call1p);
        VL_DO_DANGLING(replaceOnlyCallFunc(call2p), call2p);
    }
#endif

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        // Track all callers of each function
        m_call.main(nodep);
        //
        // In V3Hashed AstNode::user4ClearTree();        // user4p() used on entire tree
        // Iterate modules backwards, in bottom-up order.
        // Required so that a module instantiating another can benefit from collapsing.
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstNodeModule* nodep) override {
        UINFO(4, " MOD   " << nodep << endl);
        m_modp = nodep;
        m_modNFuncs = 0;
        m_walkLast2p = nullptr;
        m_hashed.clear();
        // Compute hash of all statement trees in the function
        m_state = STATE_HASH;
        iterateChildren(nodep);
        m_state = STATE_IDLE;
        if (debug() >= 9) m_hashed.dumpFilePrefixed("combine");
        // Walk the hashes removing empty functions
        walkEmptyFuncs();
        // Walk the hashes looking for duplicate functions
        walkDupFuncs();
        // Walk the statements looking for large replicated code sections
        // Note this is disabled, it still needed work
        // Also repair it for DPI functions; when make __common need to ensure proper
        // flags get inherited from the old to new AstCFunc, and that AstText doesn't
        // get split between functions causing the text to have a dangling reference.
#ifdef VL_COMBINE_STATEMENTS
        {
            m_state = STATE_DUP;
            iterateChildren(nodep);
            m_state = STATE_IDLE;
        }
#endif
        m_modp = nullptr;
    }
    virtual void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        if (!nodep->dontCombine()) {
            if (m_state == STATE_HASH) {
                hashStatement(nodep);  // Hash the entire function - it might be identical
            }
#ifdef VL_COMBINE_STATEMENTS
            else if (m_state == STATE_DUP) {
                iterateChildren(nodep);
            }
#endif
        }
    }
    virtual void visit(AstNodeStmt* nodep) override {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        if (m_state == STATE_HASH && m_cfuncp) {
            hashStatement(nodep);
        }
#ifdef VL_COMBINE_STATEMENTS
        else if (m_state == STATE_DUP && m_cfuncp) {
            walkDupCodeStart(nodep);
        }
#endif
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*) override {}
    virtual void visit(AstTraceDecl*) override {}
    virtual void visit(AstTraceInc*) override {}
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CombineVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~CombineVisitor() override {  //
        V3Stats::addStat("Optimizations, Combined CFuncs", m_statCombs);
    }
};

//######################################################################
// Combine class functions

void V3Combine::combineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CombineVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("combine", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
