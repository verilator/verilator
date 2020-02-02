// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Class's Transformations:
//
// Each module:
//   Each cell:
//      Create CUse for cell forward declaration
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3CUse.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"

#include VL_INCLUDE_UNORDERED_MAP

//######################################################################

class CUseState {
private:
    // MEMBERS
    AstNodeModule* m_modInsertp;  // Current module to insert AstCUse under
    typedef std::pair<VUseType, string> UseString;
    std::map<UseString, AstCUse*> m_didUse;  // What we already used

    // NODE STATE
    // Entire netlist:
    //  AstClass::user1()     -> bool.  True if class needs to_string dumper
    AstUser1InUse m_inuser1;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

public:
    AstCUse* newUse(AstNode* nodep, VUseType useType, const string& name) {
        UseString key(useType, name);
        if (m_didUse.find(key) == m_didUse.end()) {
            AstCUse* newp = new AstCUse(nodep->fileline(), useType, name);
            m_modInsertp->addStmtp(newp);
            UINFO(8, "Insert " << newp << endl);
            m_didUse[key] = newp;
        }
        return m_didUse[key];
    }

    // CONSTRUCTORS
    explicit CUseState(AstNodeModule* nodep)
        : m_modInsertp(nodep) {}
    virtual ~CUseState() {}
    VL_UNCOPYABLE(CUseState);
};

class CUseVisitor : public AstNVisitor {
    // MEMBERS
    CUseState m_state;  // Inserter state

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Module use builders
    void makeUseCells(AstNodeModule* nodep) {
        for (AstNode* itemp = nodep->stmtsp(); itemp; itemp = itemp->nextp()) {
            if (AstCell* cellp = VN_CAST(itemp, Cell)) {
                // Currently no include because we include __Syms which has them all
                m_state.newUse(nodep, VUseType::INT_FWD_CLASS, cellp->modp()->name());
            }
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        if (v3Global.opt.trace()) {
            AstCUse* usep
                = m_state.newUse(nodep, VUseType::INT_FWD_CLASS, v3Global.opt.traceClassBase());
            usep->protect(false);
        }
        makeUseCells(nodep);
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {}  // All in AstNodeModule

public:
    // CONSTRUCTORS
    explicit CUseVisitor(AstNodeModule* nodep)
        : m_state(nodep) {
        iterate(nodep);
    }
    virtual ~CUseVisitor() {}
    VL_UNCOPYABLE(CUseVisitor);
};

//######################################################################
// Class class functions

void V3CUse::cUseAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Call visitor separately for each module, so visitor state is cleared
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_CAST(nodep->nextp(), NodeModule)) {
        // Insert under this module; someday we should e.g. make Ast
        // for each output file and put under that
        CUseVisitor visitor(nodep);
    }
    V3Global::dumpCheckGlobalTree("cuse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
