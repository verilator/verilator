// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Class's Transformations:
//
// Each module:
//   Each cell:
//      Create CUse for cell forward declaration
//   Each class:
//      Create string access functions
//   Search for dtypes referencing class, and create CUse for forward declaraion
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3CUse.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"

#include <unordered_map>

//######################################################################

class CUseState final {
private:
    // MEMBERS
    AstNodeModule* m_modInsertp;  // Current module to insert AstCUse under
    using UseString = std::pair<VUseType, std::string>;
    std::map<const UseString, AstCUse*> m_didUse;  // What we already used

    // NODE STATE
    //  AstClass::user2()     -> bool.  True if iterated
    AstUser2InUse m_inuser2;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

public:
    AstCUse* newUse(AstNode* nodep, VUseType useType, const string& name) {
        UseString key{useType, name};
        if (m_didUse.find(key) == m_didUse.end()) {
            AstCUse* const newp = new AstCUse{nodep->fileline(), useType, name};
            m_modInsertp->addStmtp(newp);
            UINFO(8, "Insert " << newp << endl);
            m_didUse[key] = newp;
        }
        return m_didUse[key];
    }

    // CONSTRUCTORS
    explicit CUseState(AstNodeModule* nodep)
        : m_modInsertp{nodep} {}
    virtual ~CUseState() = default;
    VL_UNCOPYABLE(CUseState);
};

// Visit within a module all nodes and data types they reference, finding
// any classes so we can make sure they are defined when Verilated code
// compiles
class CUseDTypeVisitor final : public AstNVisitor {
    // MEMBERS
    CUseState& m_stater;  // State for inserter
    bool m_impOnly = false;  // In details needed only for implementation
    // METHODS
    virtual void visit(AstClassRefDType* nodep) override {
        if (nodep->user2SetOnce()) return;  // Process once
        if (!m_impOnly) m_stater.newUse(nodep, VUseType::INT_FWD_CLASS, nodep->classp()->name());
        // No class.h, it's inside the class package's h file
        m_stater.newUse(nodep, VUseType::IMP_INCLUDE, nodep->classp()->classOrPackagep()->name());
        // Need to include extends() when we implement, but no need for pointers to know
        VL_RESTORER(m_impOnly);
        {
            m_impOnly = true;
            iterateChildren(nodep->classp());  // This also gets all extend classes
        }
    }
    virtual void visit(AstNodeDType* nodep) override {
        if (nodep->user2SetOnce()) return;  // Process once
        if (nodep->virtRefDTypep()) iterate(nodep->virtRefDTypep());
        if (nodep->virtRefDType2p()) iterate(nodep->virtRefDType2p());
    }
    virtual void visit(AstNode* nodep) override {
        if (nodep->user2SetOnce()) return;  // Process once
        if (nodep->dtypep() && !nodep->dtypep()->user2()) iterate(nodep->dtypep());
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CUseDTypeVisitor(AstNodeModule* nodep, CUseState& stater)
        : m_stater(stater) {  // Need () or GCC 4.8 false warning
        iterate(nodep);
    }
    virtual ~CUseDTypeVisitor() override = default;
    VL_UNCOPYABLE(CUseDTypeVisitor);
};

class CUseVisitor final : public AstNVisitor {
    // MEMBERS
    CUseState m_state;  // Inserter state

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Module use builders
    void makeUseCells(AstNodeModule* nodep) {
        for (AstNode* itemp = nodep->stmtsp(); itemp; itemp = itemp->nextp()) {
            if (AstCell* const cellp = VN_CAST(itemp, Cell)) {
                // Currently no include because we include __Syms which has them all
                m_state.newUse(nodep, VUseType::INT_FWD_CLASS, cellp->modp()->name());
            }
        }
    }
    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        makeUseCells(nodep);
        { CUseDTypeVisitor dtypeVisitor{nodep, m_state}; }
    }
    virtual void visit(AstNode*) override {}  // All in AstNodeModule

public:
    // CONSTRUCTORS
    explicit CUseVisitor(AstNodeModule* nodep)
        : m_state{nodep} {
        iterate(nodep);
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
         modp = VN_CAST(modp->nextp(), NodeModule)) {
        // Insert under this module; someday we should e.g. make Ast
        // for each output file and put under that
        CUseVisitor visitor{modp};
    }
    V3Global::dumpCheckGlobalTree("cuse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
