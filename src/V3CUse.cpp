// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
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
#include "V3Global.h"

#include <set>

//######################################################################

// Visit within a module all nodes and data types they reference, finding
// any classes so we can make sure they are defined when Verilated code
// compiles
class CUseVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNode::user1()     -> bool.  True if already visited
    const VNUser1InUse m_inuser1;

    // MEMBERS
    bool m_impOnly = false;  // In details needed only for implementation
    AstNodeModule* const m_modp;  // Current module
    std::set<std::pair<VUseType, std::string>> m_didUse;  // What we already used

    // METHODS
    void addNewUse(AstNode* nodep, VUseType useType, const string& name) {
        if (m_didUse.emplace(useType, name).second) {
            AstCUse* const newp = new AstCUse{nodep->fileline(), useType, name};
            m_modp->addStmtp(newp);
            UINFO(8, "Insert " << newp << endl);
        }
    }

    // VISITORS
    virtual void visit(AstClassRefDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (!m_impOnly) addNewUse(nodep, VUseType::INT_FWD_CLASS, nodep->classp()->name());
        // Need to include extends() when we implement, but no need for pointers to know
        VL_RESTORER(m_impOnly);
        {
            m_impOnly = true;
            iterateChildren(nodep->classp());  // This also gets all extend classes
        }
    }
    virtual void visit(AstNodeDType* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (nodep->virtRefDTypep()) iterate(nodep->virtRefDTypep());
        if (nodep->virtRefDType2p()) iterate(nodep->virtRefDType2p());
    }
    virtual void visit(AstNode* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (nodep->dtypep() && !nodep->dtypep()->user1()) iterate(nodep->dtypep());
        iterateChildren(nodep);
    }
    virtual void visit(AstCell* nodep) override {
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
    }
    virtual ~CUseVisitor() override = default;
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
    V3Global::dumpCheckGlobalTree("cuse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
