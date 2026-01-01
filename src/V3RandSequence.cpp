// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Transform randsequence statements
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
// V3Randomize's Transformations:
//
// Convert each RandSequence production into a production task, and hookup.
//      PROD({x}) -> TASK(__Vrs_{x}, ARG(__VrsBreak), arguments)
//                      JUMPBLOCK
//
// Every variable referenced in the RandSequence becomes an ARG passed
// around. (Alternative would be make a VARXREF's but the needed variable may
// be on the stack, subject to recursion, or otherwise.)
//
// A production becomes a conditional execution of the PRODLIST below
//   for a single production list
//      RSPROD(RSRULE(weight, stmt))
//        -> IF(weight != 0, stmt)
//   or RSPROD(RSRULE(weight1, stmt!), RSRULE(weight2, stmt2))
//        -> RANDCASE(CASEITEM(weight1, stmt1), CASEITEM(weight2, stmt2))
//
// Return becomes a jump to end of production task
//      RSRETURN -> JUMPBLOCK(..., JUMPGO)
//
// Break becomes a jump to end of production task, and sets a variable
// that the production call will check
//      RSBREAK -> ASSIGH(__VrsBreak, 1)
//                 JUMPBLOCK(..., JUMPGO)
//
// Production calls become a function call
//      call({x}) -> TASKCALL(__Vrs_{x}, ARG(__VrsBreak), arguments)
//                   IF(__VrsBreak) JUMPGO-break
//
// Rand join maps to a large complicated function, described in comments below
//
// If, Case, and Repeat map to normal non-randsequence nodes
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "verilatedos.h"

#include "V3RandSequence.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Global.h"

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Matcher classes (for suggestion matching)

class RSProdMatcher final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override { return VN_IS(nodep, RSProd); }
};

//######################################################################
// Visitor that marks classes needing a randomize() method

class RandSequenceVisitor final : public VNVisitor {
    // STATE - global
    std::map<AstRSProd*, AstNodeFTask*> m_prodFuncps;  // Generated production functions

    // STATE - for current visit position (use VL_RESTORER)
    AstNodeModule* m_modp = nullptr;  // Current module
    AstRandSequence* m_rsp = nullptr;  // Current randsequence
    AstRSProd* m_startProdp = nullptr;  // Starting production
    AstNodeFTask* m_prodFuncp = nullptr;  // Production function being built
    AstJumpBlock* m_jumpBlockp = nullptr;  // Building jumpblock for return/break
    AstVar* m_breakVarp = nullptr;  // Break variable
    std::unordered_set<AstVar*> m_localizes;  // Variables to become function inouts
    std::map<std::string, AstVar*> m_localizeNames;  // Ordered names of function inouts
    std::unordered_map<const AstVar*, AstVar*> m_localizeRemaps;  // New ports for old vars

    // METHODS
    void findLocalizes(AstRandSequence* nodep) {
        std::set<AstVar*> localVars;
        nodep->foreach([&](AstNode* const nodep) {
            if (AstVarRef* const anodep = VN_CAST(nodep, VarRef)) {
                m_localizes.emplace(anodep->varp());
            } else if (AstVar* const anodep = VN_CAST(nodep, Var)) {
                localVars.emplace(anodep);
            }
        });
        // Clear every variable allocated in the RandSequence
        for (AstVar* varp : localVars) m_localizes.erase(varp);
        // Sort by name, so function arguments are stable
        for (AstVar* varp : m_localizes) {
            UINFO(9, "localize " << varp);
            m_localizeNames.emplace(varp->name(), varp);
        }
    }

    AstVar* newBreakVar(FileLine* fl, bool asOutput) {
        AstVar* const varp = new AstVar{fl, VVarType::PORT, "__VrsBreak", VFlagBitPacked{}, 1};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        varp->funcLocal(true);
        if (asOutput) varp->direction(VDirection::OUTPUT);
        AstNode* outp = varp;
        outp->addNext(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                                    new AstConst{fl, AstConst::BitFalse{}}});

        // Also add arguments as next's
        for (auto& itr : m_localizeNames) {
            const AstVar* const lvarp = itr.second;
            AstVar* const iovarp
                = new AstVar{fl, VVarType::PORT, "__Vrsarg_" + lvarp->name(), lvarp};
            iovarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            iovarp->funcLocal(true);
            iovarp->direction(VDirection::REF);
            varp->addNext(iovarp);
            m_localizeRemaps.emplace(lvarp, iovarp);
        }
        return varp;
    }

    AstTask* newStartFunc(AstRandSequence* nodep) {
        // Create wrapper that is called by the sequence
        AstTask* const taskp = new AstTask{m_startProdp->fileline(), m_rsp->name(), nullptr};
        taskp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_modp->addStmtsp(taskp);

        // Create local (not output) break variable
        VL_RESTORER(m_localizeRemaps);
        AstVar* breakVarp = newBreakVar(nodep->fileline(), false);
        taskp->addStmtsp(breakVarp);

        // Call the start production's task
        taskp->addStmtsp(newProdFuncRef(nodep, m_startProdp, breakVarp));

        UINFOTREE(9, taskp, "newStart", "");
        return taskp;
    }

    AstNode* newProdFuncRef(AstNode* nodep, AstRSProd* prodp, AstVar* breakVarp) {
        auto it = m_prodFuncps.find(prodp);
        UASSERT_OBJ(it != m_prodFuncps.end(), nodep, "No production function made");
        AstNodeFTask* const prodFuncp = it->second;
        FileLine* const fl = nodep->fileline();
        AstArg* const argsp
            = new AstArg{fl, breakVarp->name(), new AstVarRef{fl, breakVarp, VAccess::WRITE}};
        for (auto& itr : m_localizeNames) {
            const AstVar* const lvarp = itr.second;
            AstVar* const iovarp = m_localizeRemaps[lvarp];
            UASSERT_OBJ(iovarp, nodep, "No new port variable for local variable" << lvarp);
            argsp->addNext(new AstArg{nodep->fileline(), "__Vrsarg_" + lvarp->name(),
                                      new AstVarRef{fl, iovarp, VAccess::READWRITE}});
        }
        AstNode* const newp
            = new AstStmtExpr{fl, new AstTaskRef{fl, VN_AS(prodFuncp, Task), argsp}};
        return newp;
    }

    void newProdFunc(AstRSProd* nodep) {
        // Task, as time may pass
        AstTask* const newp
            = new AstTask{nodep->fileline(), m_rsp->name() + "_" + nodep->name(), nullptr};
        m_modp->addStmtsp(newp);
        m_prodFuncps.emplace(nodep, newp);
        UINFOTREE(9, newp, "newProd", "");
    }

    AstNode* newProdRandJoin(AstRSProd* prodp, AstRSProdList* prodlistp) {
        // For weight == 1.0 longer sequence (favor stay in a)
        // For weight == 0.0 shorter squence (favor change a/b)
        UASSERT_OBJ(prodlistp->weightp(), prodlistp, "Weight should have default CONST(0.5)");
        AstNodeExpr* weightp = prodlistp->weightp()->unlinkFrBack();

        // Build map of production lists and productions we need to join
        // Must mainain the relative order of each sequence.
        std::deque<AstRSProdItem*> lists;
        std::unordered_map<AstRSProdItem*, std::deque<AstNodeStmt*>> listStmts;
        for (AstRSProdItem* proditemp = VN_AS(prodlistp->prodsp(), RSProdItem); proditemp;
             proditemp = VN_AS(proditemp->nextp(), RSProdItem)) {
            lists.push_back(proditemp);
            AstRSProd* const subProdp = proditemp->prodp();
            if (!subProdp) continue;
            if (!subProdp->rulesp()) continue;
            if (!subProdp->rulesp()->prodlistsp()) continue;
            for (AstNodeStmt* subStmtp
                 = VN_AS(subProdp->rulesp()->prodlistsp()->prodsp(), NodeStmt);
                 subStmtp; subStmtp = VN_AS(subStmtp->nextp(), NodeStmt)) {
                listStmts[proditemp].push_back(subStmtp);
            }
        }

        UINFO(9, "RandJoin productions called:");
        for (AstRSProdItem* proditemp : lists) {
            UINFO(9, "  list " << proditemp);
            for (AstNodeStmt* prodp : listStmts[proditemp]) UINFO(9, "    calls " << prodp);
        }

        // Need to clone all nodes used

        FileLine* fl = prodlistp->fileline();
        AstNode* newp = nullptr;

        // "bool _Vjoin_repick = true;"  // Pick a new longer sequence
        AstVar* repickVarp = new AstVar{fl, VVarType::VAR, "_Vjoin_repick", VFlagBitPacked{}, 1};
        repickVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        repickVarp->funcLocal(true);
        m_breakVarp->addNextHere(repickVarp);  // Add to function top, not newp
        newp = AstNode::addNext(newp,
                                new AstAssign{fl, new AstVarRef{fl, repickVarp, VAccess::WRITE},
                                              new AstConst{fl, AstConst::BitTrue{}}});

        // "int _Vjoin_nleft_0 = N(items);"  // N(a) Number left to generate in list 0, starts at
        // N(list0)
        std::deque<AstVar*> nleftVarps;
        int i = 0;
        for (AstRSProdItem* proditemp : lists) {
            // 'rand join arule arule arule' is legal, so need numbered, not non-unique named
            // nleft's
            AstVar* const varp = new AstVar{
                fl, VVarType::VAR, "_Vjoin_nleft_" + std::to_string(i++), VFlagBitPacked{}, 32};
            varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            varp->funcLocal(true);
            m_breakVarp->addNextHere(varp);  // Add to function top, not newp
            nleftVarps.push_back(varp);

            newp = AstNode::addNext(
                newp,
                new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                              new AstConst{fl, AstConst::WidthedValue{}, 32,
                                           static_cast<uint32_t>(listStmts[proditemp].size())}});
        }

        // "int _Vjoin_picked_elist = 0;"  // 0 = pick first eligible (non-finished) list, 1 = pick
        // second, etc
        AstVar* const pickedVarp
            = new AstVar{fl, VVarType::VAR, "_Vjoin_picked_elist", VFlagBitPacked{}, 1};
        pickedVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        pickedVarp->funcLocal(true);
        m_breakVarp->addNextHere(pickedVarp);  // Add to function top, not newp

        // "while(1) {"  // Generate until make complete sequence
        AstJumpBlock* const whilep = new AstJumpBlock{fl, nullptr};
        newp = AstNode::addNext(newp, new AstLoop{fl, whilep});
        {
            // "if ((std::rand() & 0xffffUL) > (0xffff * weight)) _Vjoin_repick = true;"
            whilep->addStmtsp(new AstIf{
                fl,
                new AstGt{
                    fl, new AstRand{fl, AstRand::SRandomU32{}},
                    new AstRToIS{fl, new AstMulD{fl,
                                                 new AstConst{fl, AstConst::RealDouble{},
                                                              static_cast<double>(0xffffffffUL)},
                                                 weightp}}},
                new AstAssign{fl, new AstVarRef{fl, repickVarp, VAccess::WRITE},
                              new AstConst{fl, AstConst::BitTrue{}}}});

            // "if (_Vjoin_repick) {"
            AstIf* ifp = new AstIf{fl, new AstVarRef{fl, repickVarp, VAccess::READ}};
            whilep->addStmtsp(ifp);
            {
                // "// _Vjoin_nlists_eligible is how many lists eligable for picking"
                // "int _Vjoin_nlists_eligible = 0;"
                AstVar* const eligibleVarp = new AstVar{
                    fl, VVarType::VAR, "_Vjoin_nlists_eligible", VFlagBitPacked{}, 32};
                eligibleVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                eligibleVarp->funcLocal(true);
                m_breakVarp->addNextHere(eligibleVarp);  // Add to function top, not newp
                ifp->addThensp(new AstAssign{fl, new AstVarRef{fl, eligibleVarp, VAccess::WRITE},
                                             new AstConst{fl, AstConst::WidthedValue{}, 32, 0}});

                i = 0;
                for (AstRSProdItem* proditemp : lists) {
                    (void)proditemp;
                    // "_Vjoin_nlists_eligible += _Vjoin_nleft_0 ? 1 : 0;"
                    ifp->addThensp(new AstAssign{
                        fl, new AstVarRef{fl, eligibleVarp, VAccess::WRITE},
                        new AstAdd{
                            fl, new AstVarRef{fl, eligibleVarp, VAccess::READ},
                            new AstCond{
                                fl,
                                new AstNeq{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, 0},
                                           new AstVarRef{fl, nleftVarps[i], VAccess::READ}},
                                new AstConst{fl, AstConst::WidthedValue{}, 32, 1},
                                new AstConst{fl, AstConst::WidthedValue{}, 32, 0}}}});
                    ++i;
                }

                // "if (!_Vjoin_nlists_eligible) break;"  // Out of elements
                ifp->addThensp(
                    new AstIf{fl,
                              new AstEq{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, 0},
                                        new AstVarRef{fl, eligibleVarp, VAccess::READ}},
                              new AstJumpGo{fl, m_jumpBlockp}});

                // "// +1 to simplify usage, so 0 = done"
                // "_Vjoin_picked_elist = 1 + (std::rand() % _Vjoin_nlists_eligible);"
                ifp->addThensp(new AstAssign{
                    fl, new AstVarRef{fl, pickedVarp, VAccess::WRITE},
                    new AstAdd{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, 1},
                               new AstModDiv{fl, new AstRand{fl, AstRand::SRandomU32{}},
                                             new AstVarRef{fl, eligibleVarp, VAccess::READ}}}});

                // "_Vjoin_repick = false;
                ifp->addThensp(new AstAssign{fl, new AstVarRef{fl, repickVarp, VAccess::WRITE},
                                             new AstConst{fl, AstConst::BitFalse{}}});
            }

            // "// Number of eligible lists left before hit _Vjoin_picked one"
            // "int _Vjoin_sel_elist = _Vjoin_picked_elist;"
            AstVar* const selVarp
                = new AstVar{fl, VVarType::VAR, "_Vjoin_sel_elist", VFlagBitPacked{}, 32};
            selVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            selVarp->funcLocal(true);
            m_breakVarp->addNextHere(selVarp);  // Add to function top, not newp
            whilep->addStmtsp(new AstAssign{fl, new AstVarRef{fl, selVarp, VAccess::WRITE},
                                            new AstVarRef{fl, pickedVarp, VAccess::READ}});

            i = -1;
            for (AstRSProdItem* proditemp : lists) {
                ++i;
                // "if (_Vjoin_nleft_0) {"
                ifp = new AstIf{fl,
                                new AstNeq{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, 0},
                                           new AstVarRef{fl, nleftVarps[i], VAccess::READ}},
                                nullptr, nullptr};
                whilep->addStmtsp(ifp);
                {
                    // "--_Vjoin_sel_elist;"
                    ifp->addThensp(new AstAssign{
                        fl, new AstVarRef{fl, selVarp, VAccess::WRITE},
                        new AstSub{fl, new AstVarRef{fl, selVarp, VAccess::READ},
                                   new AstConst{fl, AstConst::WidthedValue{}, 32, 1}}});

                    // "if (_Vjoin_sel_elist == 0) {"
                    AstIf* const jIfp = new AstIf{
                        fl,
                        new AstEq{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, 0},
                                  new AstVarRef{fl, selVarp, VAccess::READ}},
                        nullptr, nullptr};
                    ifp->addThensp(jIfp);
                    {
                        // "switch (_Vjoin_nleft_0) {"
                        //     "case 2 / * N(a)  * /: {statement}; break;"
                        //     "case 1 / * N(a) - 1 * /: {statement}; break;"
                        uint32_t j = static_cast<uint32_t>(listStmts[proditemp].size());
                        for (AstNodeStmt* prodp : listStmts[proditemp]) {
                            jIfp->addThensp(new AstIf{
                                fl,
                                new AstEq{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, j},
                                          new AstVarRef{fl, nleftVarps[i], VAccess::READ}},
                                prodp->cloneTree(false)});
                            --j;
                        }

                        // "--_Vjoin_nleft_0;"
                        jIfp->addThensp(new AstAssign{
                            fl, new AstVarRef{fl, nleftVarps[i], VAccess::WRITE},
                            new AstSub{fl, new AstVarRef{fl, nleftVarps[i], VAccess::READ},
                                       new AstConst{fl, AstConst::WidthedValue{}, 32, 1}}});

                        // "if (0 == _Vjoin_nleft_0) _Vjoin_repick = true;"
                        jIfp->addThensp(new AstIf{
                            fl,
                            new AstEq{fl, new AstConst{fl, AstConst::WidthedValue{}, 32, 0},
                                      new AstVarRef{fl, nleftVarps[i], VAccess::READ}},
                            new AstAssign{fl, new AstVarRef{fl, repickVarp, VAccess::WRITE},
                                          new AstConst{fl, AstConst::BitTrue{}}}});

                        // "continue;"
                        jIfp->addThensp(new AstJumpGo{fl, whilep});
                    }
                }
            }
        }

        UINFOTREE(9, newp, "ForkJoin new", "-");
        return newp;
    }

    // VISITORS

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstRandSequence* nodep) override {
        UINFO(9, "visit " << nodep);
        UASSERT_OBJ(m_modp, nodep, "randsequence not under module");
        if (m_rsp) {
            // No examples found in the wild
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: randsequence under randsequence");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        UINFOTREE(9, nodep, "rsIn", "");
        VL_RESTORER(m_rsp);
        m_rsp = nodep;
        VL_RESTORER(m_startProdp);

        VL_RESTORER(m_localizes);
        VL_RESTORER(m_localizeNames);
        VL_RESTORER(m_localizeRemaps);
        findLocalizes(nodep);

        // Find first production
        m_startProdp = nodep->prodsp();
        if (nodep->prodp()) m_startProdp = nodep->prodp();  // Has a start production selected

        // Build production functions
        for (AstRSProd* prodp = nodep->prodsp(); prodp; prodp = VN_AS(prodp->nextp(), RSProd)) {
            newProdFunc(prodp);
            // Don't iterate yet, need to have tasks we can reference
        }

        // Iterate all of the new productions, moving guts into functions just made
        // Must do those with 'rand join' first, as they need to see the raw AstRS* nodes
        // before they are removed.  (Alternative would be to keep them until the end).
        UINFOTREE(9, nodep, "RS Tree pre-it", "-");
        std::unordered_set<AstRSProd*> prodHasRandJoin;
        for (AstRSProd* prodp = nodep->prodsp(); prodp; prodp = VN_AS(prodp->nextp(), RSProd)) {
            prodp->foreach([&](AstRSProdList* const prodlistp) {
                if (prodlistp->randJoin()) prodHasRandJoin.emplace(prodp);
            });
        }
        for (AstRSProd *nextp, *prodp = nodep->prodsp(); prodp; prodp = nextp) {
            nextp = VN_AS(prodp->nextp(), RSProd);
            if (prodHasRandJoin.count(prodp)) VL_DO_DANGLING(iterate(prodp), prodp);
        }
        for (AstRSProd *nextp, *prodp = nodep->prodsp(); prodp; prodp = nextp) {
            nextp = VN_AS(prodp->nextp(), RSProd);
            if (!prodHasRandJoin.count(prodp)) VL_DO_DANGLING(iterate(prodp), prodp);
        }
        UINFOTREE(9, nodep, "RS Tree post-it", "-");

        // Replace randsequence with call to randsequence start function
        AstTask* const startFuncp = newStartFunc(nodep);
        AstArg* argsp = nullptr;
        for (auto& itr : m_localizeNames) {
            AstVar* const lvarp = itr.second;
            argsp = AstNode::addNext(
                argsp, new AstArg{nodep->fileline(), "__Vrsarg_" + lvarp->name(),
                                  new AstVarRef{nodep->fileline(), lvarp, VAccess::READWRITE}});
        }
        AstTaskRef* const callStartp
            = new AstTaskRef{nodep->fileline(), startFuncp->name(), argsp};
        callStartp->taskp(startFuncp);
        nodep->replaceWith(new AstStmtExpr{nodep->fileline(), callStartp});

        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstRSProd* nodep) override {
        // Production, immediately under a randsequence
        UINFO(9, "visit " << nodep);
        UINFOTREE(9, nodep, "visit " << nodep, "-");
        UASSERT_OBJ(!m_prodFuncp, nodep, "recursive production definition?");
        VL_RESTORER(m_prodFuncp);
        auto it = m_prodFuncps.find(nodep);
        UASSERT_OBJ(it != m_prodFuncps.end(), nodep, "No production function made");
        m_prodFuncp = it->second;

        // Create a break variable
        // TODO we could do this only if break exists in the downstream production,
        // but as-is we'll optimize it away in most cases anyways
        VL_RESTORER(m_breakVarp);
        VL_RESTORER(m_localizeRemaps);
        m_breakVarp = newBreakVar(nodep->fileline(), true);
        m_prodFuncp->addStmtsp(m_breakVarp);

        // Put JumpBlock immediately under the new function to support
        // a future break/return.  V3Const will rip it out if unneeded.
        VL_RESTORER(m_jumpBlockp);
        m_jumpBlockp = new AstJumpBlock{nodep->fileline(), nullptr};
        m_prodFuncp->addStmtsp(m_jumpBlockp);

        if (nodep->fvarp())
            nodep->fvarp()->v3warn(E_UNSUPPORTED,
                                   "Unsupported: randsequence production function variable");
        if (nodep->portsp())
            nodep->portsp()->v3warn(E_UNSUPPORTED,
                                    "Unsupported: randsequence production function ports");

        // Move children into m_prodFuncp, and iterate there
        if (!nodep->rulesp()) {  // Nothing to do
        } else if (nodep->rulesp()->prodlistsp() && nodep->rulesp()->prodlistsp()->randJoin()) {
            AstRSProdList* const prodlistp = nodep->rulesp()->prodlistsp();
            AstNode* const itemsp = newProdRandJoin(nodep, prodlistp);
            m_jumpBlockp->addStmtsp(itemsp);
            iterateAndNextNull(itemsp);
        } else if (!nodep->rulesp()->nextp()) {  // Single rule/list, can just do it
            // RSPROD(RSRULE(weight, stmt)) -> IF(weight != 0, stmt)
            AstRSRule* const rulep = nodep->rulesp();
            AstNode* itemsp = nullptr;
            if (rulep->weightStmtsp()) itemsp = rulep->weightStmtsp()->unlinkFrBackWithNext();
            if (rulep->prodlistsp())
                itemsp = AstNode::addNext(itemsp, rulep->prodlistsp()->unlinkFrBackWithNext());
            // Can ignore rulep->weightp() unless is zero, in which case noop, add if
            if (rulep->weightp())
                itemsp = new AstIf{rulep->weightp()->fileline(),
                                   new AstNeq{rulep->weightp()->fileline(),
                                              new AstConst{rulep->weightp()->fileline(), 0},
                                              rulep->weightp()->unlinkFrBack()},
                                   itemsp};
            // Move prodlist to parent (m_prodFunc) and process
            if (itemsp) {
                UINFOTREE(9, itemsp, "additems", "-");
                m_jumpBlockp->addStmtsp(itemsp);
                iterateAndNextNull(itemsp);
                UINFOTREE(9, m_jumpBlockp, "jumpBlockNow", "-");
            }
        } else {
            // List of rules with "OR", need to random-weight them
            // RSPROD(RSRULE(weight1, stmt!), RSRULE(weight2, stmt2))
            //   -> RANDCASE(CASEITEM(weight1, stmt1), CASEITEM(weight2, stmt2))
            AstRandCase* const randcasep = new AstRandCase{nodep->fileline(), nullptr};
            for (AstRSRule* rulep = nodep->rulesp(); rulep;
                 rulep = VN_AS(rulep->nextp(), RSRule)) {
                AstNode* itemsp = nullptr;
                if (rulep->weightStmtsp()) itemsp = rulep->weightStmtsp()->unlinkFrBackWithNext();
                if (rulep->prodlistsp())
                    itemsp = AstNode::addNext(itemsp, rulep->prodlistsp()->unlinkFrBackWithNext());
                if (itemsp) {
                    AstNodeExpr* const weightp = rulep->weightp()
                                                     ? rulep->weightp()->unlinkFrBack()
                                                     : new AstConst{rulep->fileline(), 1};
                    randcasep->addItemsp(new AstCaseItem{rulep->fileline(), weightp, itemsp});
                }
            }
            m_jumpBlockp->addStmtsp(randcasep);
            iterateAndNextNull(randcasep);
        }

        // V3Task needs to know if we ended up making a recursive function
        m_prodFuncp->foreach([&](AstNodeFTaskRef* const nodep) {
            if (nodep->taskp() == m_prodFuncp) m_prodFuncp->recursive(true);
        });
        UINFOTREE(9, m_prodFuncp, "rsprod-task-done " << nodep, "-");

        // Done with production, should have moved everything to new task
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstRSRule* nodep) override {
        // Rule of what to produce (as a list) under a production
        nodep->v3fatalSrc("randsequence rule should be iterated and deleted by AstRSProd");
    }
    void visit(AstRSProdList* nodep) override {
        // List of productions to call, potentially with a weight
        UINFO(9, "visit " << nodep);
        UASSERT_OBJ(m_prodFuncp, nodep, "RSProdList not under production");

        // Move prodlist to parent (m_prodFunc) and process
        if (AstNode* const itemsp = nodep->prodsp()) {
            UASSERT_OBJ(!nodep->randJoin(), nodep,
                        "rand join should have been handled in visit(RSRule)");
            nodep->replaceWith(itemsp->unlinkFrBackWithNext());
            // Will soon iterate itemsp as part of normal visit process
            // These will become sequential in the generated task
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstRSProdItem* nodep) override {
        // "call" to generate using another production
        UINFO(9, "visit " << nodep);
        UASSERT_OBJ(m_prodFuncp, nodep, "RSProdItem not under production");
        AstRSProd* const foundp = nodep->prodp();
        UASSERT_OBJ(foundp, nodep, "Unlinked production reference");
        // Convert to task call
        AstNode* const newp = newProdFuncRef(nodep, foundp, m_breakVarp);
        // The production might have done a "break;", skip other steps if so
        newp->addNext(new AstIf{nodep->fileline(),
                                new AstVarRef{nodep->fileline(), m_breakVarp, VAccess::READ},
                                new AstJumpGo{nodep->fileline(), m_jumpBlockp}});

        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstRSBreak* nodep) override {
        UASSERT_OBJ(m_jumpBlockp, nodep, "RSBreak not under production jump block");
        UASSERT_OBJ(m_breakVarp, nodep, "no break variable");
        AstNodeStmt* const newp = new AstAssign{
            nodep->fileline(), new AstVarRef{nodep->fileline(), m_breakVarp, VAccess::WRITE},
            new AstConst{nodep->fileline(), AstConst::BitTrue{}}};
        newp->addNext(new AstJumpGo{nodep->fileline(), m_jumpBlockp});
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstRSReturn* nodep) override {
        UASSERT_OBJ(m_jumpBlockp, nodep, "RSReturn not under production jump block");
        nodep->replaceWith(new AstJumpGo{nodep->fileline(), m_jumpBlockp});
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstVarRef* nodep) override {
        // Change references to variables inside randsequence to references to
        // ref variables on the new task
        const auto it = m_localizeRemaps.find(nodep->varp());
        if (it != m_localizeRemaps.end()) {
            AstVar* const iovarp = it->second;
            UINFO(9, "VARREF remap " << nodep << " -> " << iovarp);
            nodep->varp(iovarp);
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit RandSequenceVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~RandSequenceVisitor() override = default;
};

//######################################################################
// RandSequence method class functions

void V3RandSequence::randSequenceNetlist(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { RandSequenceVisitor randSequenceVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("randsequence", 0, dumpTreeEitherLevel() >= 3);
}
