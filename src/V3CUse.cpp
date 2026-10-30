// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Handle SV classes
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
// V3CUse's Transformations:
//
// Each module:
//   Each cell:
//      Create CUse for cell forward declaration
//   Search for dtypes referencing class, and create CUse for forward declaration
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3CUse.h"

#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

// Visit within a module all nodes and data types they reference, finding
// any classes so we can make sure they are defined when Verilated code
// compiles
class CUseVisitor final : public VNVisitorConst {
    // NODE STATE
    //  AstNode::user1()     -> VisitState.
    const VNUser1InUse m_inuser1;

    // TYPES
    enum VisitState : std::uint8_t {
        VS_NONE,  // Not visited
        VS_IMPL,  // Visited in implementation only
        VS_FULL,  // Visited fully
    };

    // MEMBERS
    AstNodeModule* const m_modp;  // Current module
    std::map<std::string, std::pair<FileLine*, VUseType>> m_didUse;  // What we already used
    bool m_impOnly = false;  // Inside implementation, no need to include in header

    // METHODS
    bool alreadyVisited(AstNode* const nodep) const {
        const VisitState currVisitState = m_impOnly ? VS_IMPL : VS_FULL;
        if (nodep->user1() >= currVisitState) return true;
        nodep->user1(currVisitState);
        return false;
    }
    void addNewUse(const AstNode* const nodep, VUseType useType, const AstNodeModule* const modp) {
        if (m_impOnly) {
            // Implementation files include Syms header, which should have every non-class already
            // included
            if (!VN_IS(modp, Class)) return;
            useType = VUseType::IMP_INCLUDE;
        }
        auto e = m_didUse.emplace(modp->name(), std::make_pair(nodep->fileline(), useType));
        if (e.second || ((e.first->second.second & useType) != useType)) {
            e.first->second.second = e.first->second.second | useType;
        }
    }

    // VISITORS
    void visit(AstClassRefDType* nodep) override {
        addNewUse(nodep, VUseType::INT_FWD_CLASS | VUseType::IMP_INCLUDE, nodep->classp());
    }
    void visit(AstClassExtends* nodep) override {
        if (alreadyVisited(nodep)) return;
        addNewUse(nodep, VUseType::INT_INCLUDE, nodep->classp());
        iterateChildrenConst(nodep);
    }
    void visit(AstCFunc* nodep) override {
        if (alreadyVisited(nodep)) return;
        iterateAndNextConstNull(nodep->argsp());
        VL_RESTORER(m_impOnly);
        m_impOnly = true;
        // Make sure we have the types of local variables
        iterateAndNextConstNull(nodep->varsp());
        iterateAndNextConstNull(nodep->stmtsp());
    }
    void visit(AstNodeCCall* nodep) override {
        UASSERT_OBJ(m_impOnly, nodep, "Call outside of implementation file");
        if (alreadyVisited(nodep)) return;
        // Parameter types are needed even if argument has other type.
        iterateAndNextConstNull(nodep->funcp()->argsp());
        iterateConst(nodep->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstCReturn* nodep) override {
        UASSERT_OBJ(m_impOnly, nodep, "Return outside of implementation file");
        UASSERT_OBJ(!alreadyVisited(nodep), nodep, "Visited same return twice");
        iterateConst(nodep->lhsp()->dtypep());
    }
    void visit(AstNodeDType* nodep) override {
        if (alreadyVisited(nodep)) return;  // Process once
        if (nodep->virtRefDTypep()) iterateConst(nodep->virtRefDTypep());
        if (nodep->virtRefDType2p()) iterateConst(nodep->virtRefDType2p());
        if (nodep->skipRefp() != nodep) iterateConst(nodep->skipRefp());

        // Add a CUse for every struct that requires a declaration
        AstNodeUOrStructDType* const stypep = VN_CAST(nodep->skipRefp(), NodeUOrStructDType);
        if (stypep && stypep->classOrPackagep()) {
            addNewUse(nodep, VUseType::INT_INCLUDE, stypep->classOrPackagep());
            iterateChildrenConst(stypep);
        }
    }
    void visit(AstNode* nodep) override {
        if (alreadyVisited(nodep)) return;  // Process once
        if (nodep->dtypep()) iterateConst(nodep->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstCell* nodep) override {
        if (alreadyVisited(nodep)) return;  // Process once
        if (nodep->modp()->isConstPool()) return;  // Special emit rules
        // Currently no IMP_INCLUDE because we include __Syms which has them all
        addNewUse(nodep, VUseType::INT_FWD_CLASS, nodep->modp());
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CUseVisitor(AstNodeModule* modp)
        : m_modp{modp} {
        // Constant pool has no header file, so all its uses are implementation includes
        m_impOnly = modp->isConstPool();
        iterateConst(modp);
        if (AstClass* const classp = VN_CAST(modp, Class)) {
            classp->foreachMember([&](AstClass*, AstVar* varp) { iterateConst(varp->dtypep()); });
        }

        VDouble0 fwdDeclarations;
        VDouble0 intIncludes;
        VDouble0 implIncludes;
        for (const auto& used : m_didUse) {
            AstCUse* const newp = new AstCUse{used.second.first, used.second.second, used.first};
            m_modp->addStmtsp(newp);
            UINFO(8, "Insert " << newp);
            if (newp->useType().containsAny(VUseType::INT_FWD_CLASS)) ++fwdDeclarations;
            if (newp->useType().containsAny(VUseType::INT_INCLUDE)) ++intIncludes;
            if (newp->useType().containsAny(VUseType::IMP_INCLUDE)) ++implIncludes;
        }

        V3Stats::addStatSum("CUse, Interface class forward declarations", fwdDeclarations);
        V3Stats::addStatSum("CUse, Interface includes", intIncludes);
        V3Stats::addStatSum("CUse, Implementation includes", implIncludes);
    }
    ~CUseVisitor() override = default;
    VL_UNCOPYABLE(CUseVisitor);
};

//######################################################################
// Class class functions

void V3CUse::cUseAll() {
    UINFO(2, __FUNCTION__ << ":");
    // Call visitor separately for each module, so visitor state is cleared
    for (AstNodeModule* const modp : v3Global.rootp()->modulespList()) {
        // Insert under this module; someday we should e.g. make Ast
        // for each output file and put under that
        CUseVisitor{modp};
    }
    V3Global::dumpCheckGlobalTree("cuse", 0, dumpTreeEitherLevel() >= 3);
}
