// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
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
// V3CUse's Transformations:
//
// Each module:
//   Each cell:
//      Create CUse for cell forward declaration
//   Search for dtypes referencing class, and create CUse for forward declaration
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3CUse.h"

#include "V3Ast.h"
#include "V3FileLine.h"
#include "V3Global.h"

#include <map>
#include <utility>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

// Visit within a module all nodes and data types they reference, finding
// any classes so we can make sure they are defined when Verilated code
// compiles
class CUseVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNode::user1()     -> bool.  True if already visited
    const VNUser1InUse m_inuser1;

    // MEMBERS
    AstNodeModule* const m_modp;  // Current module
    std::map<std::string, std::pair<FileLine*, VUseType>> m_didUse;  // What we already used

    // METHODS
    void addNewUse(AstNode* nodep, VUseType useType, const string& name) {
        auto e = m_didUse.emplace(name, std::make_pair(nodep->fileline(), useType));
        if (e.second || ((e.first->second.second & useType) != useType)) {
            e.first->second.second = e.first->second.second | useType;
        }
    }

    // VISITORS
    void visit(AstClassRefDType* nodep) override {
        addNewUse(nodep, VUseType::INT_FWD_CLASS, nodep->classp()->name());
    }
    void visit(AstCFunc* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateAndNextNull(nodep->argsp());
        iterateAndNextNull(nodep->stmtsp());
    }
    void visit(AstCCall* nodep) override { return; }
    void visit(AstCReturn* nodep) override {
        UASSERT(!nodep->user1SetOnce(), "Visited same return twice.");
        iterate(nodep->lhsp()->dtypep());
    }
    void visit(AstNodeDType* nodep) override {
        if (nodep->virtRefDTypep()) iterate(nodep->virtRefDTypep());
        if (nodep->virtRefDType2p()) iterate(nodep->virtRefDType2p());

        // Add a CUse for every struct that requires a declaration
        AstNodeUOrStructDType* const stypep = VN_CAST(nodep->skipRefp(), NodeUOrStructDType);
        if (stypep && stypep->classOrPackagep()) {
            addNewUse(nodep, VUseType::INT_INCLUDE, stypep->classOrPackagep()->name());
            iterateChildren(stypep);
        } else if (AstClassRefDType* const classp = VN_CAST(nodep->skipRefp(), ClassRefDType)) {
            addNewUse(nodep, VUseType::INT_FWD_CLASS, classp->name());
        }
    }
    void visit(AstNode* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (nodep->dtypep()) iterate(nodep->dtypep());
        iterateChildren(nodep);
    }
    void visit(AstCell* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        // Currently no IMP_INCLUDE because we include __Syms which has them all
        addNewUse(nodep, VUseType::INT_FWD_CLASS, nodep->modp()->name());
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CUseVisitor(AstNodeModule* modp)
        : m_modp(modp) {
        iterate(modp);

        for (auto& used : m_didUse) {
            AstCUse* const newp = new AstCUse{used.second.first, used.second.second, used.first};
            m_modp->addStmtsp(newp);
            UINFO(8, "Insert " << newp << endl);
        }
    }
    ~CUseVisitor() override = default;
    VL_UNCOPYABLE(CUseVisitor);
};

//######################################################################
// Class class functions

void V3CUse::cUseAll() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Call visitor separately for each module, so visitor state is cleared
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        // Insert under this module; someday we should e.g. make Ast
        // for each output file and put under that
        CUseVisitor{modp};
    }
    V3Global::dumpCheckGlobalTree("cuse", 0, dumpTreeLevel() >= 3);
}
