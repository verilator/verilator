// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
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
    //  AstClass::user2()     -> bool.  True if iterated
    AstUser2InUse m_inuser2;

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

// Visit within a module all nodes and data types they reference, finding
// any classes so we can make sure they are defined when Verilated code
// compiles
class CUseDTypeVisitor : public AstNVisitor {
    // MEMBERS
    CUseState& m_stater;  // State for inserter
    bool m_impOnly;  // In details needed only for implementation
    // METHODS
    virtual void visit(AstClassRefDType* nodep) VL_OVERRIDE {
        if (nodep->user2SetOnce()) return;  // Process once
        if (!m_impOnly) m_stater.newUse(nodep, VUseType::INT_FWD_CLASS, nodep->classp()->name());
        // No class.h, it's inside the class package's h file
        m_stater.newUse(nodep, VUseType::IMP_INCLUDE, nodep->classp()->packagep()->name());
        // Need to include extends() when we implement, but no need for pointers to know
        bool oldImpOnly = m_impOnly;
        {
            m_impOnly = true;
            iterateChildren(nodep->classp());  // This also gets all extend classes
        }
        m_impOnly = oldImpOnly;
    }
    virtual void visit(AstNodeDType* nodep) VL_OVERRIDE {
        if (nodep->user2SetOnce()) return;  // Process once
        if (nodep->virtRefDTypep()) iterate(nodep->virtRefDTypep());
        if (nodep->virtRefDType2p()) iterate(nodep->virtRefDType2p());
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        if (nodep->user2SetOnce()) return;  // Process once
        if (nodep->dtypep() && !nodep->dtypep()->user2()) iterate(nodep->dtypep());
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CUseDTypeVisitor(AstNodeModule* nodep, CUseState& stater)
        : m_stater(stater)
        , m_impOnly(false) {
        iterate(nodep);
    }
    virtual ~CUseDTypeVisitor() {}
    VL_UNCOPYABLE(CUseDTypeVisitor);
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
    void makeVlToString(AstClass* nodep) {
        AstCFunc* funcp = new AstCFunc(nodep->fileline(), "VL_TO_STRING", NULL, "std::string");
        funcp->argTypes("const VlClassRef<" + EmitCBaseVisitor::prefixNameProtect(nodep)
                        + ">& obj");
        funcp->isMethod(false);
        funcp->isConst(false);
        funcp->isStatic(false);
        funcp->protect(false);
        AstNode* exprp = new AstCMath(nodep->fileline(), "obj ? obj->to_string() : \"null\"", 0);
        exprp->dtypeSetString();
        funcp->addStmtsp(new AstCReturn(nodep->fileline(), exprp));
        nodep->addStmtp(funcp);
    }
    void makeToString(AstClass* nodep) {
        AstCFunc* funcp = new AstCFunc(nodep->fileline(), "to_string", NULL, "std::string");
        funcp->isConst(true);
        funcp->isStatic(false);
        funcp->protect(false);
        AstNode* exprp = new AstCMath(nodep->fileline(),
                                      "std::string(\"`{\") + to_string_middle() + \"}\"", 0);
        exprp->dtypeSetString();
        funcp->addStmtsp(new AstCReturn(nodep->fileline(), exprp));
        nodep->addStmtp(funcp);
    }
    void makeToStringMiddle(AstClass* nodep) {
        AstCFunc* funcp = new AstCFunc(nodep->fileline(), "to_string_middle", NULL, "std::string");
        funcp->isConst(true);
        funcp->isStatic(false);
        funcp->protect(false);
        funcp->addStmtsp(new AstCStmt(nodep->fileline(), "std::string out;\n"));
        std::string comma;
        for (AstNode* itemp = nodep->membersp(); itemp; itemp = itemp->nextp()) {
            if (VN_IS(itemp, Var)) {
                string stmt = "out += \"";
                stmt += comma;
                comma = ", ";
                stmt += itemp->origNameProtect();
                stmt += ":\" + VL_TO_STRING(";
                stmt += itemp->nameProtect();
                stmt += ");\n";
                nodep->user1(true);  // So what we extend dumps this
                funcp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
            }
        }
        if (nodep->extendsp() && nodep->extendsp()->classp()->user1()) {
            string stmt = "out += \"";
            if (!comma.empty()) stmt += "\", \"+ ";
            // comma = ", ";  // Nothing further so not needed
            stmt += nodep->extendsp()->dtypep()->nameProtect();
            stmt += "::to_string_middle();\n";
            nodep->user1(true);  // So what we extend dumps this
            funcp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
        }
        funcp->addStmtsp(new AstCStmt(nodep->fileline(), "return out;\n"));
        nodep->addStmtp(funcp);
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        if (v3Global.opt.trace()) {
            AstCUse* usep
                = m_state.newUse(nodep, VUseType::INT_FWD_CLASS, v3Global.opt.traceClassBase());
            usep->protect(false);
        }
        makeUseCells(nodep);
        { CUseDTypeVisitor dtypeVisitor(nodep, m_state); }
        if (AstClass* classp = VN_CAST(nodep, Class)) {
            makeVlToString(classp);
            makeToString(classp);
            makeToStringMiddle(classp);
        }
    }
    virtual void visit(AstNode*) VL_OVERRIDE {}  // All in AstNodeModule

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
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_CAST(modp->nextp(), NodeModule)) {
        // Insert under this module; someday we should e.g. make Ast
        // for each output file and put under that
        CUseVisitor visitor(modp);
    }
    V3Global::dumpCheckGlobalTree("cuse", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
