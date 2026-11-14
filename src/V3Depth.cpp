// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Depth's Transformations:
//
// Each module:
//      For each wide OP, assign a temporary variable.
//      For each deep expression, assign expression to temporary.
//      Before recursive width/const walks, break a deep spine into temps
//      using an explicit heap stack. Those walks are one C frame per node,
//      and the default 8MB stack cannot hold a chain of around ten thousand
//      binary operators. The later CFunc pass still only sees shallow trees.
// Each CFunc:
//      Any statements that need "this" are marked non-static
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Depth.h"

#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class DepthVisitor final : public VNVisitor {
    // NODE STATE

    // STATE - for current visit position (use VL_RESTORER)
    AstCFunc* m_cfuncp = nullptr;  // Current block
    AstNode* m_stmtp = nullptr;  // Current statement
    int m_depth = 0;  // How deep in an expression
    int m_maxdepth = 0;  // Maximum depth in an expression
    V3UniqueNames m_tempNames;  // For generating unique temporary variable names

    // METHODS

    void createDeepTemp(AstNodeExpr* nodep) {
        UINFO(6, "  Deep  " << nodep);
        // UINFOTREE(9, nodep, "", "deep");
        AstVar* const varp = new AstVar{nodep->fileline(), VVarType::STMTTEMP,
                                        m_tempNames.get(nodep), nodep->dtypep()};
        if (m_cfuncp) {
            m_cfuncp->addVarsp(varp);
        } else {
            nodep->v3fatalSrc("Deep expression not under a function");
        }
        // Replace node tree with reference to var
        AstVarRef* const newp = new AstVarRef{nodep->fileline(), varp, VAccess::READ};
        nodep->replaceWith(newp);
        // Put assignment before the referencing statement
        AstAssign* const assp = new AstAssign{
            nodep->fileline(), new AstVarRef{nodep->fileline(), varp, VAccess::WRITE}, nodep};
        m_stmtp->addHereThisAsNext(assp);
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_depth);
        VL_RESTORER(m_maxdepth);
        m_cfuncp = nodep;
        m_depth = 0;
        m_maxdepth = 0;
        m_tempNames.reset();
        iterateChildren(nodep);
    }
    void visitStmt(AstNodeStmt* nodep) {
        VL_RESTORER(m_stmtp);
        VL_RESTORER(m_depth);
        VL_RESTORER(m_maxdepth);
        m_stmtp = nodep;
        m_depth = 0;
        m_maxdepth = 0;
        iterateChildren(nodep);
    }
    void visit(AstNodeStmt* nodep) override { visitStmt(nodep); }
    void visit(AstSFormatArg* nodep) override { iterateChildren(nodep); }  // Don't split
    // Operators
    void visit(AstNodeTermop* nodep) override {}
    void visit(AstNodeExpr* nodep) override {
        // We have some operator defines that use 2 parens, so += 2.
        {
            VL_RESTORER(m_depth);
            m_depth += 2;
            if (m_depth > m_maxdepth) m_maxdepth = m_depth;
            iterateChildren(nodep);
        }
        if (m_stmtp && (v3Global.opt.compLimitParens() >= 1)  // Else compiler doesn't need it
            && (m_maxdepth - m_depth) > v3Global.opt.compLimitParens()
            && !VN_IS(nodep->backp(), NodeStmt)  // Not much point if we're about to use it
        ) {
            m_maxdepth = m_depth;
            createDeepTemp(nodep);
        }
    }

    //--------------------
    // Marking of non-static functions (because they might need "this")
    // (Here instead of new visitor after V3Descope just to avoid another visitor)
    void needNonStaticFunc(AstNode* nodep) {
        UASSERT_OBJ(m_cfuncp, nodep, "Non-static accessor not under a function");
        // DPI export implementations are always invoked via the generic DPI dispatcher,
        // which can only ever supply the symbol table pointer, never a scope-specific
        // "this", so they must remain static regardless of what they contain.
        if (m_cfuncp->isStatic() && !m_cfuncp->dpiExportImpl()) {
            UINFO(5, "Mark non-public due to " << nodep);
            m_cfuncp->isStatic(false);
        }
    }
    void visit(AstCExprUser* nodep) override {
        needNonStaticFunc(nodep);
        iterateChildren(nodep);
    }
    void visit(AstCStmtUser* nodep) override {
        needNonStaticFunc(nodep);
        visitStmt(nodep);
    }

    //--------------------
    // Default: Just iterate
    void visit(AstVar*) override {}  // Don't hit varrefs under vars
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DepthVisitor(AstNetlist* nodep)
        : m_tempNames{"__Vdeeptemp"} {
        iterate(nodep);
        // Extracting expressions can effect purity
        VIsCached::clearCacheTree();
    }
    ~DepthVisitor() override = default;
};

//######################################################################
// Depth class functions

//######################################################################
// Break deep expression spines before recursive visitors.

// A chain longer than this fits in the default 8MB stack. A flat 6000-input
// OR elaborates; 12000 segfaults in WidthVisitor's final walk.
static constexpr int DEPTH_BREAK_LIMIT = 1024;
static uint32_t s_deepTempCount = 0;

static void pushExprChildren(std::vector<std::pair<AstNode*, int>>& stack, AstNode* nodep,
                              int depth) {
    AstNode* const ops[4] = {nodep->op4p(), nodep->op3p(), nodep->op2p(), nodep->op1p()};
    for (AstNode* const opp : ops) {
        std::vector<AstNode*> sibs;
        for (AstNode* sibp = opp; sibp; sibp = sibp->nextp()) sibs.push_back(sibp);
        for (auto it = sibs.rbegin(); it != sibs.rend(); ++it) {
            stack.emplace_back(*it, depth + 1);
        }
    }
}

static AstNodeExpr* findDeepExpr(AstNodeExpr* rootp) {
    std::vector<std::pair<AstNode*, int>> stack;
    stack.emplace_back(rootp, 1);
    while (!stack.empty()) {
        AstNode* const nodep = stack.back().first;
        const int depth = stack.back().second;
        stack.pop_back();
        if (depth >= DEPTH_BREAK_LIMIT && nodep != rootp) {
            AstNodeExpr* const exprp = VN_CAST(nodep, NodeExpr);
            if (exprp && exprp->dtypep() && !VN_IS(exprp, Const) && !VN_IS(exprp, NodeVarRef)) {
                return exprp;
            }
        }
        if (nodep) pushExprChildren(stack, nodep, depth);
    }
    return nullptr;
}

static AstNodeAssign* cutDeepExpr(AstNodeExpr* exprp, AstNodeAssign* insertBeforep,
                                  AstNodeModule* modp, bool markWidthed) {
    FileLine* const flp = exprp->fileline();
    AstNodeDType* const dtypep = exprp->dtypep();
    UASSERT_OBJ(dtypep, exprp, "Deep expression has no dtype to name a temporary");
    const std::string name = "__Vdeepbrk" + cvtToStr(++s_deepTempCount);
    AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};
    varp->noSubst(true);
    modp->addStmtsp(varp);

    AstVarRef* const readp = new AstVarRef{flp, varp, VAccess::READ};
    AstVarRef* const writep = new AstVarRef{flp, varp, VAccess::WRITE};
    exprp->replaceWith(readp);
    AstNodeAssign* assignp;
    if (VN_IS(insertBeforep, AssignW)) {
        assignp = new AstAssignW{flp, writep, exprp};
    } else {
        assignp = new AstAssign{flp, writep, exprp};
    }
    insertBeforep->addHereThisAsNext(assignp);
    if (markWidthed) {
        varp->didWidth(true);
        readp->dtypeFrom(varp);
        writep->dtypeFrom(varp);
        readp->didWidth(true);
        writep->didWidth(true);
        assignp->dtypeFrom(varp);
        assignp->didWidth(true);
    }
    return assignp;
}

std::vector<AstNodeAssign*> V3Depth::breakDeepAssign(AstNodeAssign* assignp, AstNodeModule* modp,
                                                     bool markWidthed) {
    std::vector<AstNodeAssign*> created;
    std::vector<AstNodeAssign*> work;
    work.push_back(assignp);
    for (size_t i = 0; i < work.size(); ++i) {
        while (AstNodeExpr* const deepp = findDeepExpr(work[i]->rhsp())) {
            AstNodeAssign* const newp = cutDeepExpr(deepp, work[i], modp, markWidthed);
            created.push_back(newp);
            work.push_back(newp);
        }
    }
    return created;
}

void V3Depth::breakDeepExprs(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    std::vector<std::pair<AstNode*, AstNodeModule*>> stack;
    stack.emplace_back(nodep, nullptr);
    while (!stack.empty()) {
        AstNode* const headp = stack.back().first;
        AstNodeModule* const modp = stack.back().second;
        stack.pop_back();
        for (AstNode* np = headp; np; np = np->nextp()) {
            if (AstNodeModule* const newModp = VN_CAST(np, NodeModule)) {
                stack.emplace_back(newModp->stmtsp(), newModp);
                continue;
            }
            if (AstNodeAssign* const assignp = VN_CAST(np, NodeAssign)) {
                if (modp && assignp->rhsp()) (void)breakDeepAssign(assignp, modp, true);
            }
            AstNode* const kids[4] = {np->op4p(), np->op3p(), np->op2p(), np->op1p()};
            for (AstNode* const kidp : kids) {
                if (kidp && !VN_IS(kidp, NodeExpr)) stack.emplace_back(kidp, modp);
            }
        }
    }
}

void V3Depth::depthAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { DepthVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("depth", 0, dumpTreeEitherLevel() >= 6);
}
