// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Find broken links in tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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
//      Check local variables in CFuncs appear before they are referenced
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3Broken.h"

#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Generation counter for AstNode::m_brokenState

static class BrokenCntGlobal {
    // This is a 7 bit generation counter, stored in the bottom 7 bits of AstNode::m_brokenState,
    // used to mark a node as being present under the root AstNetlist in the current traversal. A
    // value 0 is invalid, as the AstNode constructor uses that to initialize m_brokenState
    static constexpr uint8_t MIN_VALUE = 1;
    static constexpr uint8_t MAX_VALUE = 127;

    uint8_t m_count = MIN_VALUE;

public:
    uint8_t get() const VL_MT_SAFE {
        UASSERT(MIN_VALUE <= m_count && m_count <= MAX_VALUE, "Invalid generation number");
        return m_count;
    }

    void inc() {
        ++m_count;
        if (m_count > MAX_VALUE) m_count = MIN_VALUE;
    }
} s_brokenCntGlobal;

static bool s_brokenAllowMidvisitorCheck = false;

//######################################################################
// Table of allocated AstNode pointers

static class AllocTable final {
    // MEMBERS
    std::unordered_set<const AstNode*> m_allocated;  // Set of all nodes allocated but not freed

public:
    // METHODS
    void addNewed(const AstNode* nodep) {
        // Called by operator new on any node - only if VL_LEAK_CHECKS
        // LCOV_EXCL_START
        if (VL_UNCOVERABLE(!m_allocated.emplace(nodep).second)) {
            nodep->v3fatalSrc("Newing AstNode object that is already allocated");
        }
        // LCOV_EXCL_STOP
    }
    void deleted(const AstNode* nodep) {
        // Called by operator delete on any node - only if VL_LEAK_CHECKS
        // LCOV_EXCL_START
        if (VL_UNCOVERABLE(m_allocated.erase(nodep) == 0)) {
            nodep->v3fatalSrc("Deleting AstNode object that was not allocated or already freed");
        }
        // LCOV_EXCL_STOP
    }
    bool isAllocated(const AstNode* nodep) const { return m_allocated.count(nodep) != 0; }
    void checkForLeaks() {
        if (!v3Global.opt.debugCheck()) return;

        const uint8_t brokenCntCurrent = s_brokenCntGlobal.get();

        // Those with backp() are probably under a parent that was leaked and has no backp()
        for (const bool withBack : {false, true}) {
            for (const AstNode* const nodep : m_allocated) {
                // LCOV_EXCL_START
                // Most likely not leaked, so check that first
                if (VL_UNCOVERABLE(nodep->brokenState() != brokenCntCurrent)) {
                    const bool hasBack = nodep->backp() != nullptr;
                    if (hasBack != withBack) continue;
                    // Use only AstNode::dump instead of the virtual one, as there
                    // may be varp() and other cross links that are bad.
                    // When get this message, find what forgot to delete the
                    // node by running GDB, where for node "<e###>" use:
                    //    watch *(AstNode::s_editCntGbl)==####
                    //    run
                    //    bt
                    std::cerr << "%Error: LeakedNode"
                              << (withBack ? " with back pointer: " : ": ");
                    nodep->AstNode::dump(std::cerr);
                    std::cerr << endl;
                    V3Error::incErrors();
                }
                // LCOV_EXCL_STOP
            }
        }
    }
} s_allocTable;

void V3Broken::addNewed(const AstNode* nodep) { s_allocTable.addNewed(nodep); }
void V3Broken::deleted(const AstNode* nodep) { s_allocTable.deleted(nodep); }

//######################################################################
// Table of AstNode pointers that can be linked to via member pointers

static class LinkableTable final {
    // MEMBERS
    std::unordered_set<const AstNode*> m_linkable;  // Set of all nodes allocated but not freed

public:
    // METHODS
    void clear() { m_linkable.clear(); }
    void addLinkable(const AstNode* nodep) { m_linkable.emplace(nodep); }
    bool isLinkable(const AstNode* nodep) const { return m_linkable.count(nodep) != 0; }
} s_linkableTable;

bool V3Broken::isLinkable(const AstNode* nodep) { return s_linkableTable.isLinkable(nodep); }

//######################################################################
// Check every node in tree

class BrokenCheckVisitor final : public VNVisitorConst {
    // Constants for marking we are under/not under a node
    const uint8_t m_brokenCntCurrentNotUnder = s_brokenCntGlobal.get();  // Top bit is clear
    const uint8_t m_brokenCntCurrentUnder = m_brokenCntCurrentNotUnder | 0x80;  // Top bit is set

    // STATE - across all visitors
    // All local variables declared in current function
    std::set<const AstVar*> m_localVars;
    // Variable references in current function that do not reference an in-scope local
    std::map<const AstVar*, const AstNodeVarRef*> m_suspectRefs;
    // Local variables declared in the scope of the current statement
    std::vector<std::unordered_set<const AstVar*>> m_localsStack;

    // STATE - for current visit position (use VL_RESTORER)
    const AstCFunc* m_cfuncp = nullptr;  // Current CFunc, if any
    bool m_inScope = false;  // Under AstScope
    std::set<std::string> m_cFuncNames;  // CFunc by name in current class/module

private:
    // METHODS
    static void checkWidthMin(const AstNode* nodep) {
        UASSERT_OBJ(nodep->width() == nodep->widthMin()
                        || v3Global.widthMinUsage() != VWidthMinUsage::MATCHES_WIDTH,
                    nodep, "Width != WidthMin");
    }

    void processEnter(AstNode* nodep) {
        nodep->brokenState(m_brokenCntCurrentUnder);
        const char* const whyp = nodep->broken();
        UASSERT_OBJ(!whyp, nodep,
                    "Broken link in node (or something without maybePointedTo): " << whyp);
        if (!s_brokenAllowMidvisitorCheck) nodep->checkIter();
        if (nodep->dtypep()) {
            UASSERT_OBJ(nodep->dtypep()->brokeExists(), nodep,
                        "Broken link in node->dtypep() to " << cvtToHex(nodep->dtypep()));
            UASSERT_OBJ(nodep->dtypep(), nodep,
                        "Non-dtype link in node->dtypep() to " << cvtToHex(nodep->dtypep()));
        }
        if (v3Global.assertDTypesResolved()) {
            if (nodep->hasDType()) {
                UASSERT_OBJ(nodep->dtypep(), nodep,
                            "No dtype on node with hasDType(): " << nodep->prettyTypeName());
            } else {
                UASSERT_OBJ(!nodep->dtypep(), nodep,
                            "DType on node without hasDType(): " << nodep->prettyTypeName());
            }
            UASSERT_OBJ(!nodep->getChildDTypep(), nodep,
                        "childDTypep() non-null on node after should have removed");
            if (const AstNodeDType* const dnodep = VN_CAST(nodep, NodeDType))
                checkWidthMin(dnodep);
        }
        checkWidthMin(nodep);
    }
    void processExit(AstNode* nodep) { nodep->brokenState(m_brokenCntCurrentNotUnder); }
    void processAndIterate(AstNode* nodep) {
        processEnter(nodep);
        iterateChildrenConst(nodep);
        processExit(nodep);
    }
    void processAndIterateList(AstNode* nodep) {
        while (nodep) {
            processAndIterate(nodep);
            nodep = nodep->nextp();
        }
    }
    void pushLocalScope() {
        if (m_cfuncp) m_localsStack.emplace_back();
    }
    void popLocalScope() {
        if (m_cfuncp) m_localsStack.pop_back();
    }
    bool isInScopeLocal(const AstVar* varp) const {
        for (const auto& set : m_localsStack) {
            if (set.count(varp)) return true;
        }
        return false;
    }
    // VISITORS
    void visit(AstNodeAssign* nodep) override {
        processAndIterate(nodep);
        UASSERT_OBJ(!(v3Global.assertDTypesResolved() && nodep->brokeLhsMustBeLvalue()
                      && VN_IS(nodep->lhsp(), NodeVarRef)
                      && !VN_AS(nodep->lhsp(), NodeVarRef)->access().isWriteOrRW()),
                    nodep, "Assignment LHS is not an lvalue");
    }
    void visit(AstRelease* nodep) override {
        processAndIterate(nodep);
        UASSERT_OBJ(!(v3Global.assertDTypesResolved() && VN_IS(nodep->lhsp(), NodeVarRef)
                      && !VN_AS(nodep->lhsp(), NodeVarRef)->access().isWriteOrRW()),
                    nodep, "Release LHS is not an lvalue");
    }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_inScope);
        m_inScope = true;
        VL_RESTORER(m_cFuncNames);
        m_cFuncNames.clear();
        processAndIterate(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_cFuncNames);
        m_cFuncNames.clear();
        processAndIterate(nodep);
    }
    void visit(AstNodeUOrStructDType* nodep) override {
        VL_RESTORER(m_cFuncNames);
        m_cFuncNames.clear();
        processAndIterate(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        processAndIterate(nodep);
        // m_inScope because some Vars have initial variable references without scopes
        // This might false fire with some debug flags, as not certain we don't have temporary
        // clear varScopep's during some an infrequent dump just before we re-LinkDot.
        UASSERT_OBJ(
            !(v3Global.assertScoped() && m_inScope && nodep->varp() && !nodep->varScopep()), nodep,
            "VarRef missing VarScope pointer");
        if (m_cfuncp) {
            // Check if variable is an in-scope local, otherwise mark as suspect
            if (const AstVar* const varp = nodep->varp()) {
                if (!isInScopeLocal(varp)) {
                    // This only stores the first ref for each Var, which is what we want
                    m_suspectRefs.emplace(varp, nodep);
                }
            }
        }
    }
    void visit(AstCFunc* nodep) override {
        UASSERT_OBJ(!m_cfuncp, nodep, "Nested AstCFunc");
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        m_localVars.clear();
        m_suspectRefs.clear();
        m_localsStack.clear();
        pushLocalScope();

        // Check for duplicate names, otherwise linker might just ignore them
        string nameArgs = nodep->name();
        if (!nodep->argTypes().empty()) nameArgs += "(" + nodep->argTypes() + ")";
        UASSERT_OBJ(m_cFuncNames.emplace(nameArgs).second, nodep,
                    "Duplicate cfunc name: '" << nameArgs << "'");

        processAndIterate(nodep);

        // Check suspect references are all to non-locals
        for (const auto& pair : m_suspectRefs) {
            UASSERT_OBJ(m_localVars.count(pair.first) == 0, pair.second,
                        "Local variable not in scope where referenced: " << pair.first);
        }
    }
    void visit(AstNodeIf* nodep) override {
        // Each branch is a separate local variable scope
        pushLocalScope();
        processEnter(nodep);
        processAndIterate(nodep->condp());
        if (AstNode* const thensp = nodep->thensp()) {
            pushLocalScope();
            processAndIterateList(thensp);
            popLocalScope();
        }
        if (AstNode* const elsesp = nodep->elsesp()) {
            pushLocalScope();
            processAndIterateList(elsesp);
            popLocalScope();
        }
        processExit(nodep);
        popLocalScope();
    }
    void visit(AstNodeStmt* nodep) override {
        // For local variable checking act as if any statement introduces a new scope.
        // This is aggressive but conservatively correct.
        pushLocalScope();
        processAndIterate(nodep);
        popLocalScope();
    }
    void visit(AstVar* nodep) override {
        processAndIterate(nodep);
        if (m_cfuncp) {
            m_localVars.insert(nodep);
            m_localsStack.back().insert(nodep);
        }
    }
    void visit(AstNode* nodep) override {
        // Process not just iterate
        processAndIterate(nodep);
    }

public:
    // CONSTRUCTORS
    explicit BrokenCheckVisitor(AstNetlist* nodep) { iterateConstNull(nodep); }
    ~BrokenCheckVisitor() override = default;
};

//######################################################################
// Broken check entry point

void V3Broken::brokenAll(AstNetlist* nodep) {
    // UINFO(9, __FUNCTION__ << ": " << endl);
    static bool inBroken = false;
    if (VL_UNCOVERABLE(inBroken)) {
        // A error called by broken can recurse back into broken; avoid this
        UINFO(1, "Broken called under broken, skipping recursion.\n");  // LCOV_EXCL_LINE
    } else {
        inBroken = true;

        // Mark every node in the tree
        const uint8_t brokenCntCurrent = s_brokenCntGlobal.get();
        nodep->foreach([brokenCntCurrent](AstNode* nodep) {
#ifdef VL_LEAK_CHECKS
            UASSERT_OBJ(s_allocTable.isAllocated(nodep), nodep,
                        "AstNode is in tree, but not allocated");
#endif
            UASSERT_OBJ(nodep->brokenState() != brokenCntCurrent, nodep,
                        "AstNode is already in tree at another location");
            if (nodep->maybePointedTo()) s_linkableTable.addLinkable(nodep);
            nodep->brokenState(brokenCntCurrent);
        });

        // Check every node in tree
        const BrokenCheckVisitor cvisitor{nodep};

        s_allocTable.checkForLeaks();
        s_linkableTable.clear();
        s_brokenCntGlobal.inc();
        inBroken = false;
    }
}

void V3Broken::allowMidvisitorCheck(bool flag) { s_brokenAllowMidvisitorCheck = flag; }

//######################################################################
// Self test

void V3Broken::selfTest() {
    // Exercise addNewed and deleted for coverage, as otherwise only used with VL_LEAK_CHECKS
    FileLine* const fl = new FileLine{FileLine::commandLineFilename()};
    const AstNode* const newp = new AstBegin{fl, "[EditWrapper]", nullptr};
    addNewed(newp);
    deleted(newp);
    VL_DO_DANGLING(delete newp, newp);
}
