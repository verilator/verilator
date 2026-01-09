// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Removal of named begin blocks
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Begin's Transformations:
//
// Each module:
//      Look for BEGINs
//          BEGIN(VAR...) -> VAR ... {renamed}
//      FOR -> WHILEs
//      Move static function variables and their AstInitialStatic blocks before a function
//
// There are two scopes; named BEGINs change %m and variable scopes.
// Unnamed BEGINs change only variable, not $display("%m") scope.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Begin.h"

#include "V3Stats.h"
#include "V3String.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class BeginState final {
    // NODE STATE
    // Entire netlist:
    // AstNodeFTask::user1      -> bool, 1=processed
    const VNUser1InUse m_inuser1;
    bool m_anyFuncInBegin = false;

public:
    BeginState() = default;
    ~BeginState() = default;
    void userMarkChanged(AstNode* nodep) {
        nodep->user1(true);
        m_anyFuncInBegin = true;
    }
    bool anyFuncInBegin() const { return m_anyFuncInBegin; }
};

//######################################################################

class BeginVisitor final : public VNVisitor {
    // NODE STATE
    // AstCase::user1   -> bool, if already purified

    V3UniqueNames m_caseTempNames;  // For generating unique temporary variable names used by cases
    // STATE - across all visitors
    BeginState* const m_statep;  // Current global state

    // STATE - for current visit position (use VL_RESTORER)
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNode* m_liftedp = nullptr;  // Local  nodes we are lifting into m_ftaskp
    string m_displayScope;  // Name of %m in $display/AstScopeName
    string m_namedScope;  // Name of begin blocks above us
    string m_unnamedScope;  // Name of begin blocks, including unnamed blocks
    int m_ifDepth = 0;  // Current if depth
    bool m_keepBegins = false;  // True if begins should not be inlined
    VDouble0 m_statPurifiedCaseExpr;  // Count of purified case expressions

    // METHODS

    string dot(const string& a, const string& b) { return VString::dot(a, "__DOT__", b); }

    void dotNames(const std::string& name, FileLine* const flp, const char* const blockName) {
        UINFO(8, "nname " << m_namedScope);
        // If unneeded unnamed block, whatever that means :)
        if (name == "") return;

        // Create data for dotted variable resolution
        std::string dottedname = name + "__DOT__";  // So always found
        std::string::size_type pos;
        while ((pos = dottedname.find("__DOT__")) != std::string::npos) {
            const std::string ident = dottedname.substr(0, pos);
            dottedname = dottedname.substr(pos + std::strlen("__DOT__"));
            if (name != "") {
                m_displayScope = dot(m_displayScope, ident);
                m_namedScope = dot(m_namedScope, ident);
            }
            m_unnamedScope = dot(m_unnamedScope, ident);
            // Create CellInline for dotted var resolution
            if (!m_ftaskp) {
                AstCellInline* const inlinep = new AstCellInline{flp, m_unnamedScope, blockName};
                m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
            }
        }
    }

    void liftNode(AstNode* nodep) {
        nodep->unlinkFrBack();
        if (m_ftaskp) {
            // AstBegin under ftask, just move into the ftask
            if (!m_liftedp) {
                m_liftedp = nodep;
            } else {
                m_liftedp->addNext(nodep);
            }
        } else {
            // Move to module
            m_modp->addStmtsp(nodep);
        }
    }

    // VISITORS
    void visit(AstFork* nodep) override {
        dotNames(nodep->name(), nodep->fileline(), "__FORK__");
        iterateAndNextNull(nodep->stmtsp());
        {
            // Keep begins in forks to group their statements together
            VL_RESTORER(m_keepBegins);
            m_keepBegins = true;
            iterateAndNextNull(nodep->forksp());
        }
        nodep->name("");
    }
    void visit(AstForeach* nodep) override {
        VL_DO_DANGLING(V3Begin::convertToWhile(nodep), nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        // Keep begin under assignment (in nodep->timingControlp())
        VL_RESTORER(m_keepBegins);
        m_keepBegins = true;
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_caseTempNames);
        m_modp = nodep;
        // Rename it (e.g. class under a generate)
        if (m_unnamedScope != "") {
            nodep->name(dot(m_unnamedScope, nodep->name()));
            UINFO(8, "     rename to " << nodep->name());
            m_statep->userMarkChanged(nodep);
        }
        VL_RESTORER(m_displayScope);
        VL_RESTORER(m_namedScope);
        VL_RESTORER(m_unnamedScope);
        m_displayScope = "";
        m_namedScope = "";
        m_unnamedScope = "";
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        UINFO(8, "  " << nodep);
        // Rename it
        if (m_unnamedScope != "") {
            nodep->name(dot(m_unnamedScope, nodep->name()));
            UINFO(8, "     rename to " << nodep->name());
            m_statep->userMarkChanged(nodep);
        }
        // BEGIN wrapping a function rename that function, but don't affect
        // the inside function's variables.  We then restart with empty
        // naming; so that any begin's inside the function will rename
        // inside the function.
        // Process children
        VL_RESTORER(m_displayScope);
        VL_RESTORER(m_ftaskp);
        VL_RESTORER(m_liftedp);
        VL_RESTORER(m_namedScope);
        VL_RESTORER(m_unnamedScope);
        VL_RESTORER(m_caseTempNames);
        m_displayScope = dot(m_displayScope, nodep->name());
        m_namedScope = "";
        m_unnamedScope = "";
        m_ftaskp = nodep;
        m_liftedp = nullptr;
        iterateChildren(nodep);
        nodep->foreach([&](AstInitialStatic* const initp) {
            initp->unlinkFrBack();
            m_ftaskp->addHereThisAsNext(initp);
        });
        if (m_liftedp) {
            // Place lifted nodes at beginning of stmtsp, so Var nodes appear before referenced
            if (AstNode* const stmtsp = nodep->stmtsp()) {
                stmtsp->unlinkFrBackWithNext();
                m_liftedp->addNext(stmtsp);
            }
            nodep->addStmtsp(m_liftedp);
            m_liftedp = nullptr;
        }
    }
    void visit(AstGenBlock* nodep) override {
        // GenBlocks were only useful in variable creation, change names and delete
        UINFO(8, "  " << nodep);
        VL_RESTORER(m_displayScope);
        VL_RESTORER(m_namedScope);
        VL_RESTORER(m_unnamedScope);
        UASSERT_OBJ(!m_keepBegins, nodep, "Should be able to eliminate all AstGenBlock");
        dotNames(nodep->name(), nodep->fileline(), "__BEGIN__");
        iterateAndNextNull(nodep->itemsp());
        // Repalce node with body then delete
        if (AstNode* const itemsp = nodep->itemsp()) {
            nodep->addNextHere(itemsp->unlinkFrBackWithNext());
        }
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstBegin* nodep) override {
        // Begin blocks were only useful in variable creation, change names and delete
        UINFO(8, "  " << nodep);
        VL_RESTORER(m_displayScope);
        VL_RESTORER(m_namedScope);
        VL_RESTORER(m_unnamedScope);
        {
            VL_RESTORER(m_keepBegins);
            m_keepBegins = false;
            dotNames(nodep->name(), nodep->fileline(), "__BEGIN__");
            iterateChildren(nodep);
        }

        // Cleanup
        if (m_keepBegins) {
            nodep->name("");
            return;
        }
        AstNode* addsp = nullptr;
        if (AstNode* const declsp = nodep->declsp()) {
            declsp->unlinkFrBackWithNext();
            addsp = AstNode::addNext(addsp, declsp);
        }
        if (AstNode* const stmtsp = nodep->stmtsp()) {
            stmtsp->unlinkFrBackWithNext();
            addsp = AstNode::addNext(addsp, stmtsp);
        }
        if (addsp) {
            nodep->replaceWith(addsp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstVar* nodep) override {
        // If static variable, move it outside a function.
        if (nodep->lifetime().isStatic() && m_ftaskp) {
            const std::string newName
                = m_ftaskp->name() + "__Vstatic__" + dot(m_unnamedScope, nodep->name());
            nodep->name(newName);
            nodep->unlinkFrBack();
            m_ftaskp->addHereThisAsNext(nodep);
            nodep->funcLocal(false);
        } else if (m_unnamedScope != "") {
            // Rename it
            nodep->name(dot(m_unnamedScope, nodep->name()));
            m_statep->userMarkChanged(nodep);
            // Move it under enclosing tree
            liftNode(nodep);
        }
    }
    void visit(AstTypedef* nodep) override {
        if (m_unnamedScope != "") {
            // Rename it
            nodep->name(dot(m_unnamedScope, nodep->name()));
            m_statep->userMarkChanged(nodep);
            // Move it under enclosing tree
            liftNode(nodep);
        }
    }
    void visit(AstCell* nodep) override {
        UINFO(8, "   CELL " << nodep);
        if (m_namedScope != "") {
            m_statep->userMarkChanged(nodep);
            // Rename it
            nodep->name(dot(m_namedScope, nodep->name()));
            UINFO(8, "     rename to " << nodep->name());
            // Move to module
            nodep->unlinkFrBack();
            m_modp->addStmtsp(nodep);
        }
        iterateChildren(nodep);
    }
    void visit(AstVarXRef* nodep) override {
        UINFO(9, "   VARXREF " << nodep);
        if (m_namedScope != "" && nodep->inlinedDots() == "" && !m_ftaskp) {
            nodep->inlinedDots(m_namedScope);
            UINFO(9, "    rescope to " << nodep);
        }
    }
    void visit(AstNodeFTaskRef* nodep) override {
        UINFO(9, "   FTASKREF " << nodep);
        if (m_namedScope != "" && nodep->inlinedDots() == "" && !m_ftaskp) {
            nodep->inlinedDots(m_namedScope);
            UINFO(9, "    rescope to " << nodep);
        }
        iterateChildren(nodep);
    }
    void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        // Similar code in V3Inline
        if (nodep->user1SetOnce()) return;  // Don't double-add text's
        // DPI svGetScope doesn't include function name, but %m does
        const std::string scname = nodep->forFormat() ? m_displayScope : m_namedScope;
        // To keep correct visual order, must add before exising
        if (!scname.empty()) nodep->scopeAttr("__DOT__"s + scname + nodep->scopeAttr());
        iterateChildren(nodep);
    }
    void visit(AstNodeCoverDecl* nodep) override {
        // Don't need to fix path in coverage statements, they're not under
        // any BEGINs, but V3Coverage adds them all under the module itself.
        iterateChildren(nodep);
    }
    void visit(AstCase* nodep) override {
        // Introduce temporary variable for AstCase if needed - it is done here and not in V3Case
        // because this phase is before V3Scope and V3Case is not. Doing it before V3Scope ensures
        // that V3Scope will take care of a scope creation
        if (!nodep->exprp()->isPure() && !nodep->user1SetOnce()) {
            ++m_statPurifiedCaseExpr;
            FileLine* const fl = nodep->exprp()->fileline();
            AstVar* const varp = new AstVar{fl, VVarType::XTEMP, m_caseTempNames.get(nodep),
                                            nodep->exprp()->dtypep()};
            nodep->exprp(new AstExprStmt{fl,
                                         new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                                                       nodep->exprp()->unlinkFrBack()},
                                         new AstVarRef{fl, varp, VAccess::READ}});
            if (m_ftaskp) {
                varp->funcLocal(true);
                varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                m_ftaskp->stmtsp()->addHereThisAsNext(varp);
            } else {
                m_modp->stmtsp()->addHereThisAsNext(varp);
            }
        }
        iterateChildren(nodep);
    }
    // VISITORS - LINT CHECK
    void visit(AstIf* nodep) override {  // not AstNodeIf; other types not covered
        VL_RESTORER(m_keepBegins);
        m_keepBegins = false;
        // Check IFDEPTH warning - could be in other transform files if desire
        VL_RESTORER(m_ifDepth);
        if (m_ifDepth == -1 || v3Global.opt.ifDepth() < 1) {  // Turned off
        } else if (nodep->uniquePragma() || nodep->unique0Pragma() || nodep->priorityPragma()) {
            m_ifDepth = -1;
        } else if (++m_ifDepth > v3Global.opt.ifDepth()) {
            nodep->v3warn(IFDEPTH,
                          "Deep 'if' statement; suggest unique/priority to avoid slow logic");
            nodep->fileline()->modifyWarnOff(V3ErrorCode::IFDEPTH, true);  // Warn only once
            m_ifDepth = -1;
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override {
        VL_RESTORER(m_keepBegins);
        m_keepBegins = false;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    BeginVisitor(AstNetlist* nodep, BeginState* statep)
        : m_caseTempNames{"__VCase"}
        , m_statep{statep} {
        iterate(nodep);
        V3Stats::addStatSum("Impure case expressions", m_statPurifiedCaseExpr);
    }
    ~BeginVisitor() override = default;
};

//######################################################################

class BeginRelinkVisitor final : public VNVisitorConst {
    // Replace tasks with new pointer
private:
    // NODE STATE
    //  Input:
    //   AstNodeFTask::user1p           // Node replaced, rename it

    // VISITORS
    void visit(AstNodeFTaskRef* nodep) override {
        UASSERT_OBJ(nodep->taskp(), nodep, "unlinked");
        if (nodep->taskp()->user1()) {  // It was converted
            UINFO(9, "    relinkFTask " << nodep);
            nodep->name(nodep->taskp()->name());
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstVarRef* nodep) override {
        if (nodep->varp()->user1()) {  // It was converted
            UINFO(9, "    relinVarRef " << nodep);
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstIfaceRefDType* nodep) override {
        // May have changed cell names
        // TypeTable is always after all modules, so names are stable
        UINFO(8, "   IFACEREFDTYPE " << nodep);
        if (nodep->cellp()) nodep->cellName(nodep->cellp()->name());
        UINFO(8, "       rename to " << nodep);
        iterateChildrenConst(nodep);
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    BeginRelinkVisitor(AstNetlist* nodep, BeginState*) { iterateConst(nodep); }
    ~BeginRelinkVisitor() override = default;
};

//######################################################################
// Task class functions

void V3Begin::debeginAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        BeginState state;
        { BeginVisitor{nodep, &state}; }
        if (state.anyFuncInBegin()) BeginRelinkVisitor{nodep, &state};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("begin", 0, dumpTreeEitherLevel() >= 3);
}

static AstNode* createForeachLoop(AstNodeForeach* nodep, AstNode* bodysp, AstVar* varp,
                                  AstNodeExpr* leftp, AstNodeExpr* rightp, VNType nodeType) {
    FileLine* const fl = varp->fileline();
    AstNodeExpr* varRefp = new AstVarRef{fl, varp, VAccess::READ};
    AstNodeExpr* condp;
    bool inc = true;
    switch (nodeType) {
    case VNType::LteS: condp = new AstLteS{fl, varRefp, rightp}; break;
    case VNType::Lt: condp = new AstLt{fl, varRefp, rightp}; break;
    case VNType::GteS:
        condp = new AstGteS{fl, varRefp, rightp};
        inc = false;
        break;
    default: varp->v3fatalSrc("Missing comparison handling"); break;
    }
    AstNodeExpr* incp;
    if (inc)
        incp = new AstAdd{fl, varRefp->cloneTree(false), new AstConst{fl, 1}};
    else
        incp = new AstSub{fl, varRefp->cloneTree(false), new AstConst{fl, 1}};

    AstLoop* const loopp = new AstLoop{fl};
    loopp->addStmtsp(new AstLoopTest{fl, loopp, condp});
    loopp->addStmtsp(bodysp);
    loopp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, incp});
    AstNode* const stmtsp = varp;  // New statements for outer loop
    stmtsp->addNext(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, leftp});
    stmtsp->addNext(loopp);
    return stmtsp;
}
static AstNode* createForeachLoopRanged(AstNodeForeach* nodep, AstNode* bodysp, AstVar* varp,
                                        const VNumRange& declRange) {
    FileLine* const fl = varp->fileline();
    V3Number left{nodep, 32}, right{nodep, 32};
    left.isSigned(true);
    right.isSigned(true);
    left.setLongS(declRange.left());
    right.setLongS(declRange.right());
    AstNodeExpr* const leftp = new AstConst{fl, left};
    AstNodeExpr* const rightp = new AstConst{fl, right};
    return createForeachLoop(nodep, bodysp, varp, leftp, rightp,
                             declRange.left() <= declRange.right() ? VNType::LteS : VNType::GteS);
}
AstNode* V3Begin::convertToWhile(AstForeach* nodep) {
    // UINFOTREE(1, nodep, "", "foreach-old");
    const AstSelLoopVars* const loopsp = VN_CAST(nodep->arrayp(), SelLoopVars);
    UASSERT_OBJ(loopsp, nodep, "No loop variables under foreach");
    AstNodeExpr* const fromp = loopsp->fromp();
    UASSERT_OBJ(fromp->dtypep(), fromp, "Missing data type");
    AstNodeDType* fromDtp = fromp->dtypep()->skipRefp();
    // Split into for loop
    // We record where the body needs to eventually go with bodyPointp
    AstNode* bodyPointp = new AstBegin{nodep->fileline(), "[EditWrapper]", nullptr, false};
    AstNode* newp = nullptr;
    AstNode* lastp = nodep;
    AstVar* nestedIndexp = nullptr;
    // subfromp used to traverse each dimension of multi-d variable-sized unpacked array (queue,
    // dyn-arr and associative-arr)
    AstNodeExpr* subfromp = fromp->cloneTreePure(false);
    // Major dimension first
    for (AstNode *argsp = loopsp->elementsp(), *next_argsp; argsp; argsp = next_argsp) {
        next_argsp = argsp->nextp();
        const bool empty = VN_IS(argsp, Empty);
        AstVar* const varp = VN_CAST(argsp, Var);
        UASSERT_OBJ(varp || empty, argsp, "Missing foreach loop variable");
        if (varp) varp->unlinkFrBack()->usedLoopIdx(true);
        UASSERT_OBJ(fromDtp, argsp, "more loop vars than dimensions");
        fromDtp = fromDtp->skipRefp();

        FileLine* const fl = argsp->fileline();
        if (varp) {
            AstNode* loopp = nullptr;
            VNRelinker handle;
            lastp->unlinkFrBack(&handle);
            if (const AstNodeArrayDType* const adtypep = VN_CAST(fromDtp, NodeArrayDType)) {
                loopp = createForeachLoopRanged(nodep, bodyPointp, varp, adtypep->declRange());
            } else if (const AstBasicDType* const adtypep = VN_CAST(fromDtp, BasicDType)) {
                if (adtypep->isString()) {
                    AstConst* const leftp = new AstConst{fl, 0};
                    AstNodeExpr* const rightp = new AstLenN{fl, fromp->cloneTreePure(false)};
                    loopp = createForeachLoop(nodep, bodyPointp, varp, leftp, rightp, VNType::Lt);
                } else {
                    UASSERT_OBJ(adtypep->isRanged(), varp, "foreach on basic " << adtypep);
                    loopp = createForeachLoopRanged(nodep, bodyPointp, varp, adtypep->declRange());
                }
            } else if (VN_IS(fromDtp, DynArrayDType) || VN_IS(fromDtp, QueueDType)) {
                AstConst* const leftp = new AstConst{fl, 0};
                AstNodeExpr* const rightp = new AstCMethodHard{
                    fl,
                    VN_IS(subfromp->dtypep(), NodeArrayDType)
                        ? new AstArraySel{fl, subfromp->cloneTreePure(false),
                                          new AstVarRef{fl, nestedIndexp, VAccess::READ}}
                        : subfromp->cloneTreePure(false),
                    VCMethod::DYN_SIZE};
                AstVarRef* varRefp = new AstVarRef{fl, varp, VAccess::READ};
                subfromp = new AstCMethodHard{fl, subfromp, VCMethod::ARRAY_AT, varRefp};
                subfromp->dtypep(fromDtp);
                rightp->dtypeSetSigned32();
                rightp->protect(false);
                loopp = createForeachLoop(nodep, bodyPointp, varp, leftp, rightp, VNType::Lt);
            } else if (VN_IS(fromDtp, AssocArrayDType)) {
                // Make this: var KEY_TYPE index;
                //            bit index__Vfirst;
                //            index__Vfirst = 0;
                //            if (0 != array.first(index))
                //                 do body while (index__Vfirst || 0 != array.next(index))
                AstVar* const first_varp = new AstVar{
                    fl, VVarType::BLOCKTEMP, varp->name() + "__Vfirst", VFlagBitPacked{}, 1};
                first_varp->usedLoopIdx(true);
                first_varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                AstNodeExpr* const firstp
                    = new AstCMethodHard{fl, subfromp->cloneTreePure(false), VCMethod::ASSOC_FIRST,
                                         new AstVarRef{fl, varp, VAccess::READWRITE}};
                firstp->dtypeSetSigned32();
                AstNodeExpr* const nextp
                    = new AstCMethodHard{fl, subfromp->cloneTreePure(false), VCMethod::ASSOC_NEXT,
                                         new AstVarRef{fl, varp, VAccess::READWRITE}};
                nextp->dtypeSetSigned32();
                AstVarRef* varRefp = new AstVarRef{fl, varp, VAccess::READ};
                subfromp = new AstCMethodHard{fl, subfromp, VCMethod::ARRAY_AT, varRefp};
                subfromp->dtypep(fromDtp);
                AstNode* const first_clearp
                    = new AstAssign{fl, new AstVarRef{fl, first_varp, VAccess::WRITE},
                                    new AstConst{fl, AstConst::BitFalse{}}};
                AstLogOr* const orp
                    = new AstLogOr{fl, new AstVarRef{fl, first_varp, VAccess::READ},
                                   new AstNeq{fl, new AstConst{fl, 0}, nextp}};
                AstLoop* const lp = new AstLoop{fl};
                lp->addStmtsp(new AstLoopTest{fl, lp, orp});
                lp->addStmtsp(first_clearp);
                first_clearp->addNext(bodyPointp);
                AstNode* const ifbodyp
                    = new AstAssign{fl, new AstVarRef{fl, first_varp, VAccess::WRITE},
                                    new AstConst{fl, AstConst::BitTrue{}}};
                ifbodyp->addNext(lp);
                loopp = varp;
                loopp->addNext(first_varp);
                loopp->addNext(
                    new AstIf{fl, new AstNeq{fl, new AstConst{fl, 0}, firstp}, ifbodyp});
            }
            UASSERT_OBJ(loopp, argsp, "unable to foreach " << fromDtp);
            // New loop goes UNDER previous loop
            handle.relink(loopp);
            lastp = bodyPointp;
            if (!newp) newp = loopp;
        }
        // Prep for next
        nestedIndexp = varp;
        fromDtp = fromDtp->subDTypep();
    }
    VL_DO_DANGLING(subfromp->deleteTree(), subfromp);
    // The parser validates we don't have "foreach (array[,,,])"
    AstNode* const bodyp = nodep->stmtsp();
    if (!newp) {
        nodep->v3warn(NOEFFECT, "foreach with no loop variable has no effect");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        if (!bodyPointp->backp()) VL_DO_DANGLING(bodyPointp->deleteTree(), bodyPointp);
        return nullptr;
    }
    if (bodyp) {
        bodyPointp->replaceWith(bodyp->unlinkFrBackWithNext());
    } else {
        bodyPointp->unlinkFrBack();
    }
    VL_DO_DANGLING(bodyPointp->deleteTree(), bodyPointp);
    VL_DO_DANGLING(nodep->deleteTree(), nodep);
    // UINFOTREE(1, newp, "", "foreach-new");
    return newp;
}
