// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Reuse wide temporaries created by V3Premit
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// Optimize wide temporaries in cases when V3Expand cannot handle them,
// ie. for wide temporaries are not expanded due to their width exceeding
// expandLimit.
//
// Note: this phase requires temporaries in a single static assignment form (SSA).
//
// V3Reuse's Transformations:
//
// Each function:
//      Collect all temporaries and insert them to freeTemps pool.
//      For each temporary write operation:
//          Find temporary which does not have pending READ operation
//          ie. exists in freeTemps pool.
//              If not found, create one with appropriate size.
//          Replace temporary with recently found one.
//          Replace dtype of a temporary with old one to use old width.
//          Mark temporary as replaced and remove from freeTemps pool.
//      For each temporary read operation:
//          If temporary was recently replaced, find replacee and replace it.
//          Replace dtype of a temporary with old one to use old width.
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3Reuse.h"

#include "V3Global.h"
#include "V3Stats.h"
#include "V3ThreadPool.h"

VL_DEFINE_DEBUG_FUNCTIONS;

const string TEMP_PREFIX = "__Vtemp_";  // Prefix for temporary variables.

class ReuseVisitor final : public VNVisitor {
    // TYPES
    using WidthType = int;
    using TempIdType = size_t;
    using IdTempMap = std::map<TempIdType, AstVar*>;

    // MEMBERS
    AstCFunc* const m_cfuncp;  // Current function.

    // STATE
    std::map<WidthType, IdTempMap, std::greater<WidthType>>
        m_freeTemps;  // Freed temporaries eligible for reuse.
    std::map<WidthType, IdTempMap, std::greater<WidthType>>
        m_replacedInStmt;  // Temporaries replaced in a current statement.
    std::unordered_map<AstVar*, AstVar*> m_replaced;  // Mapping of vars replaced in the previous
                                                      // WRITE operation to be used in READ.
    TempIdType m_tmpVarCnt = 0;  // Counter for temporary ids.
    std::unordered_set<AstVar*> m_removedTemps;  // No longer needed temporaries to be deleted.
    VDouble0 m_totalTemps;  // Statistic for how many temps were before cleanup.

    // STATIC METHODS
    static TempIdType idFrom(const AstNode* nodep) {
        UASSERT(VString::startsWith(nodep->name(), TEMP_PREFIX),
                "Prefix must start with '" + TEMP_PREFIX + "'");
        const auto it = nodep->name().find_last_of('_');
        UASSERT(it != string::npos, "Unexpected temp name format: " + nodep->name());
        const string idStr = nodep->name().substr(it + 1, nodep->name().size());
        std::istringstream iss(idStr);
        TempIdType id;
        iss >> id;
        UASSERT(iss, "Unexpected temp name format: " + nodep->name());
        return id;
    }
    static bool isWideTemp(const AstVar* nodep) {
        return nodep && nodep->isStatementTemp() && nodep->isWide()
               && VN_IS(nodep->dtypep(), BasicDType);
    }
    static bool isExcluded(AstVar* varp) { return varp && varp->user1(); }
    static void excludeVars(AstCFunc* nodep) {
        nodep->foreach([](AstCCall* ccallp) {
            for (AstNode* argsp = ccallp->argsp(); argsp; argsp = argsp->nextp()) {
                if (AstVarRef* refp = VN_CAST(argsp, VarRef)) {
                    if (refp->varp()) refp->varp()->user1SetOnce();
                }
            }
        });
    }
    static void fixupType(AstVarRef* nodep, AstVar* varp) {
        // Swap varp of current VarRef and preserve dtype to use old width.
        AstNodeDType* prevDtypep = nodep->dtypep();
        nodep->varp(varp);
        nodep->dtypep(prevDtypep);
    }

    // METHODS
    AstVar* createWideTemp(FileLine* fl, AstNodeDType* dtypep) {
        // To avoid naming clashes with previously created temporaries, interfix is added.
        const string name = TEMP_PREFIX + "clean_" + std::to_string(++m_tmpVarCnt);
        AstVar* const varp = new AstVar{fl, VVarType::STMTTEMP, name, dtypep};
        m_cfuncp->addInitsp(varp);
        return varp;
    }
    void addFreedTemps() {
        // After a statement, all read temporaries used in it are freed.
        // This is to avoid situation when multiple variables are replaced
        // with the same replacee in one statement.
        for (const auto& replaced : m_replacedInStmt) {
            const WidthType& key = replaced.first;
            const IdTempMap& temps = replaced.second;
            m_freeTemps[key].insert(temps.cbegin(), temps.cend());
        }
    }
    void removeUnusedVars() {
        for (AstVar* varp : m_removedTemps) {
            VL_DO_DANGLING(varp->unlinkFrBack()->deleteTree(), varp);
        }
    }

    // VISITORS
    void visit(AstIf* nodep) override {
        // Temp may be reused when READ was in a non-taken branch.
        m_replacedInStmt.clear();
        iterateAndNextConstNull(nodep->condp());
        addFreedTemps();

        m_replacedInStmt.clear();
        iterateAndNextConstNull(nodep->thensp());
        addFreedTemps();

        m_replacedInStmt.clear();
        iterateAndNextConstNull(nodep->elsesp());
        addFreedTemps();
    }
    void visit(AstNodeStmt* nodep) override {
        m_replacedInStmt.clear();
        iterateChildren(nodep);
        addFreedTemps();
    }
    void visit(AstVar* nodep) override {
        if (!isWideTemp(nodep)) return;
        UINFO(5, "Populating free temp from declaration: " << nodep << endl);

        if (!isExcluded(nodep)) {
            m_freeTemps[nodep->width()][idFrom(nodep)] = nodep;
            m_removedTemps.emplace(nodep);
        }

        if (v3Global.opt.stats()) ++m_totalTemps;
    }
    void visit(AstVarRef* nodep) override {
        if (!isWideTemp(nodep->varp()) || isExcluded(nodep->varp())) return;

        if (nodep->access().isWriteOnly()) {
            auto matchingCandidates = m_freeTemps.begin();
            if (matchingCandidates == m_freeTemps.end() || matchingCandidates->second.empty()
                || matchingCandidates->first < nodep->width()) {
                // If we didn't find candidate with appropriate width, create one.
                AstVar* const varp = createWideTemp(nodep->fileline(), nodep->dtypep());
                const auto it
                    = m_freeTemps.emplace(nodep->width(), IdTempMap{{idFrom(varp), varp}});
                matchingCandidates = it.first;
            }

            UASSERT(matchingCandidates != m_freeTemps.end() && !matchingCandidates->second.empty(),
                    "Candidate for substitution should be available or created previously");

            const auto candidate = matchingCandidates->second.begin();
            UINFO(5, "Replacing WRITE temp " << nodep->varp() << " with: " << candidate->second
                                             << endl);

            AstVar* const varp = candidate->second;

            m_replaced.emplace(nodep->varp(), varp);
            matchingCandidates->second.erase(candidate);
            if (matchingCandidates->second.empty()) m_freeTemps.erase(matchingCandidates);

            fixupType(nodep, varp);
        } else if (nodep->access().isReadOnly()) {
            auto it = m_replaced.find(nodep->varp());
            if (it != m_replaced.end()) {
                UINFO(5,
                      "Replacing READ temp " << nodep->varp() << " with: " << it->second << endl);

                AstVar* const varp = it->second;
                m_replacedInStmt[varp->width()].emplace(idFrom(varp), varp);
                m_replaced.erase(it);

                // Mark this var as used to prevent deletion of it later.
                m_removedTemps.erase(varp);

                fixupType(nodep, varp);

                // Avoid substitution to prevent errors in partial word updates.
                nodep->varp()->noSubst(true);
            }
        }
    }
    void visit(AstConstPool*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ReuseVisitor(AstCFunc* nodep)
        : m_cfuncp{nodep} {
        excludeVars(nodep);
        iterate(nodep);
        removeUnusedVars();
    }
    ~ReuseVisitor() override {
        if (v3Global.opt.stats()) {
            V3Stats::addStatSum("Optimizations, Reuse total wide temps", m_totalTemps);
            V3Stats::addStatSum("Optimizations, Reuse removed temps",
                                VDouble0{m_removedTemps.size()});
        }
    }
};

//######################################################################
// V3Reuse class functions

void V3Reuse::reuseAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        V3ThreadScope threadScope;
        VNUser1InUse inUse;

        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (AstCFunc* const cfuncp = VN_CAST(nodep, CFunc)) {
                    threadScope.enqueue([cfuncp]() { ReuseVisitor{cfuncp}; });
                }
            }
        }
    }
    V3Global::dumpCheckGlobalTree("reuse", 0, dumpTreeEitherLevel() >= 3);
}
