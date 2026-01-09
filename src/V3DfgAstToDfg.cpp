// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert AstModule to DfgGraph
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
//
// Convert and AstModule (before V3Scope), or the entire AstNetlist
// (after V3Scope) to an initial DfgGraph composed onlyof DfgLogic,
// DfgUnresolved and DfgVertexVar vertices. This will later be synthesized
// into primitive operations by V3DfgPasses::synthesize.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Cfg.h"
#include "V3Const.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"

#include <iterator>

VL_DEFINE_DEBUG_FUNCTIONS;

template <bool T_Scoped>
class AstToDfgVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar/AstVarScope::user2() -> DfgVertexVar* : the corresponding variable vertex
    // AstVar/AstVarScope::user3() -> bool : Already gathered - used fine grained below
    const VNUser2InUse m_user2InUse;

    // TYPES
    using RootType = std::conditional_t<T_Scoped, AstNetlist, AstModule>;
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgAstToDfgContext& m_ctx;  // The context for stats
    AstScope* m_scopep = nullptr;  // The current scope, iff T_Scoped

    // METHODS
    static Variable* getTarget(const AstVarRef* refp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(refp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(refp->varp());
        }
    }

    std::unique_ptr<std::vector<Variable*>> getLiveVariables(const CfgGraph& cfg) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            std::unique_ptr<std::vector<AstVarScope*>> result = V3Cfg::liveVarScopes(cfg);
            const auto resultp = reinterpret_cast<std::vector<Variable*>*>(result.release());
            return std::unique_ptr<std::vector<Variable*>>{resultp};
        } else {
            std::unique_ptr<std::vector<AstVar*>> result = V3Cfg::liveVars(cfg);
            const auto resultp = reinterpret_cast<std::vector<Variable*>*>(result.release());
            return std::unique_ptr<std::vector<Variable*>>{resultp};
        }
    }

    // Mark variables referenced under node
    static void markReferenced(const AstNode* nodep) {
        nodep->foreach([](const AstVarRef* refp) {
            Variable* const tgtp = getTarget(refp);
            // Mark as read from non-DFG logic
            if (refp->access().isReadOrRW()) DfgVertexVar::setHasModRdRefs(tgtp);
            // Mark as written from non-DFG logic
            if (refp->access().isWriteOrRW()) DfgVertexVar::setHasModWrRefs(tgtp);
        });
    }

    DfgVertexVar* getVarVertex(Variable* varp) {
        if (!varp->user2p()) {
            // TODO: fix this up when removing the different flavours of DfgVar
            const AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
            DfgVertexVar* const vtxp
                = VN_IS(dtypep, UnpackArrayDType)
                      ? static_cast<DfgVertexVar*>(new DfgVarArray{m_dfg, varp})
                      : static_cast<DfgVertexVar*>(new DfgVarPacked{m_dfg, varp});
            varp->user2p(vtxp);
        }
        return varp->user2u().template to<DfgVertexVar*>();
    }

    // Gather variables written by the given logic node.
    // Return nullptr if any are not supported.
    std::unique_ptr<std::vector<DfgVertexVar*>> gatherWritten(const AstNode* nodep) {
        const VNUser3InUse user3InUse;
        std::unique_ptr<std::vector<DfgVertexVar*>> resp{new std::vector<DfgVertexVar*>{}};
        // We can ignore AstVarXRef here. The only thing we can do with DfgLogic is
        // synthesize it into regular vertices, which will fail on a VarXRef at that point.
        const bool abort = nodep->exists([&](const AstNodeVarRef* vrefp) -> bool {
            if (VN_IS(vrefp, VarXRef)) return true;
            if (vrefp->access().isReadOnly()) return false;
            Variable* const varp = getTarget(VN_AS(vrefp, VarRef));
            if (!V3Dfg::isSupported(varp)) return true;
            if (!varp->user3SetOnce()) resp->emplace_back(getVarVertex(varp));
            return false;
        });
        if (abort) {
            ++m_ctx.m_nonRepVar;
            return nullptr;
        }
        return resp;
    }

    // Gather variables read by the given logic node.
    // Return nullptr if any are not supported.
    std::unique_ptr<std::vector<DfgVertexVar*>> gatherRead(const AstNode* nodep) {
        const VNUser3InUse user3InUse;
        std::unique_ptr<std::vector<DfgVertexVar*>> resp{new std::vector<DfgVertexVar*>{}};
        // We can ignore AstVarXRef here. The only thing we can do with DfgLogic is
        // synthesize it into regular vertices, which will fail on a VarXRef at that point.
        const bool abort = nodep->exists([&](const AstNodeVarRef* vrefp) -> bool {
            if (VN_IS(vrefp, VarXRef)) return true;
            if (vrefp->access().isWriteOnly()) return false;
            Variable* const varp = getTarget(VN_AS(vrefp, VarRef));
            if (!V3Dfg::isSupported(varp)) return true;
            if (!varp->user3SetOnce()) resp->emplace_back(getVarVertex(varp));
            return false;
        });
        if (abort) {
            ++m_ctx.m_nonRepVar;
            return nullptr;
        }
        return resp;
    }

    // Gather variables live in to the given CFG.
    // Return nullptr if any are not supported.
    std::unique_ptr<std::vector<DfgVertexVar*>> gatherLive(const CfgGraph& cfg) {
        // Run analysis
        std::unique_ptr<std::vector<Variable*>> varps = getLiveVariables(cfg);
        if (!varps) {
            ++m_ctx.m_nonRepLive;
            return nullptr;
        }

        // Convert to vertics
        const VNUser3InUse user3InUse;
        std::unique_ptr<std::vector<DfgVertexVar*>> resp{new std::vector<DfgVertexVar*>{}};
        resp->reserve(varps->size());
        for (Variable* const varp : *varps) {
            if (!V3Dfg::isSupported(varp)) {
                ++m_ctx.m_nonRepVar;
                return nullptr;
            }
            UASSERT_OBJ(!varp->user3SetOnce(), varp, "Live variables should be unique");
            resp->emplace_back(getVarVertex(varp));
        }
        return resp;
    }

    // Connect inputs and outputs of a DfgLogic
    void connect(DfgLogic& vtx, const std::vector<DfgVertexVar*>& iVarps,
                 const std::vector<DfgVertexVar*>& oVarps) {
        // Connect inputs
        for (DfgVertexVar* const iVarp : iVarps) vtx.addInput(iVarp);
        // Connect outputs
        for (DfgVertexVar* const oVarp : oVarps) {
            if (!oVarp->srcp()) oVarp->srcp(new DfgUnresolved{m_dfg, oVarp});
            oVarp->srcp()->as<DfgUnresolved>()->addDriver(&vtx);
        }
    }

    // Convert AstAlways to DfgLogic, return true if successful.
    bool convert(AstAlways* nodep) {
        const VAlwaysKwd kwd = nodep->keyword();
        if (kwd == VAlwaysKwd::CONT_ASSIGN) {
            // TODO: simplify once CFG analysis can handle arrays
            if (const AstAssignW* const ap = VN_CAST(nodep->stmtsp(), AssignW)) {
                if (ap->nextp()) return false;
                // Cannot handle assignment with timing control
                if (ap->timingControlp()) return false;
                // Potentially convertible block
                ++m_ctx.m_inputs;
                // Gather written variables, give up if any are not supported
                const std::unique_ptr<std::vector<DfgVertexVar*>> oVarpsp = gatherWritten(ap);
                if (!oVarpsp) return false;
                // Gather read variables, give up if any are not supported
                const std::unique_ptr<std::vector<DfgVertexVar*>> iVarpsp = gatherRead(ap);
                if (!iVarpsp) return false;
                // Create the DfgLogic
                DfgLogic* const logicp = new DfgLogic{m_dfg, nodep, m_scopep, nullptr};
                // Connect it up
                connect(*logicp, *iVarpsp, *oVarpsp);
                // Done
                ++m_ctx.m_representable;
                return true;
            }
        }

        // Can only handle combinational logic
        if (nodep->sentreep()) return false;
        if (kwd != VAlwaysKwd::ALWAYS && kwd != VAlwaysKwd::ALWAYS_COMB) return false;

        // Potentially convertible block
        ++m_ctx.m_inputs;
        // Attempt to build CFG of AstAlways, give up if failed
        std::unique_ptr<CfgGraph> cfgp = CfgGraph::build(nodep->stmtsp());
        if (!cfgp) {
            ++m_ctx.m_nonRepCfg;
            return false;
        }
        // Gather written variables, give up if any are not supported
        const std::unique_ptr<std::vector<DfgVertexVar*>> oVarpsp = gatherWritten(nodep);
        if (!oVarpsp) return false;
        // Gather read variables, give up if any are not supported
        const std::unique_ptr<std::vector<DfgVertexVar*>> iVarpsp = gatherLive(*cfgp);
        if (!iVarpsp) return false;
        // Create the DfgLogic
        DfgLogic* const logicp = new DfgLogic{m_dfg, nodep, m_scopep, std::move(cfgp)};
        // Connect it up
        connect(*logicp, *iVarpsp, *oVarpsp);
        // Done
        ++m_ctx.m_representable;
        return true;
    }

    // VISITORS
    // Unhandled node
    void visit(AstNode* nodep) override { markReferenced(nodep); }

    // Containers to descend through to find logic constructs
    void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    void visit(AstModule* nodep) override { iterateAndNextNull(nodep->stmtsp()); }
    void visit(AstIface* nodep) override {
        if (!nodep->hasVirtualRef()) {
            iterateAndNextNull(nodep->stmtsp());
        } else {
            markReferenced(nodep);
        }
    }
    void visit(AstTopScope* nodep) override { iterate(nodep->scopep()); }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstActive* nodep) override {
        if (nodep->hasCombo()) {
            iterateChildren(nodep);
        } else {
            markReferenced(nodep);
        }
    }

    // Non-representable constructs
    void visit(AstCell* nodep) override { markReferenced(nodep); }
    void visit(AstNodeProcedure* nodep) override { markReferenced(nodep); }

    // Potentially representable constructs
    void visit(AstAlways* nodep) override {
        if (!convert(nodep)) markReferenced(nodep);
    }

    // CONSTRUCTOR
    AstToDfgVisitor(DfgGraph& dfg, RootType& root, V3DfgAstToDfgContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {
        iterate(&root);
    }
    VL_UNCOPYABLE(AstToDfgVisitor);
    VL_UNMOVABLE(AstToDfgVisitor);

public:
    static void apply(DfgGraph& dfg, RootType& root, V3DfgAstToDfgContext& ctx) {
        // Convert all logic under 'root'
        AstToDfgVisitor{dfg, root, ctx};
        // Remove unread and undriven variables (created when something failed to convert)
        for (DfgVertexVar* const varp : dfg.varVertices().unlinkable()) {
            if (!varp->srcp() && !varp->hasSinks()) VL_DO_DANGLING(varp->unlinkDelete(dfg), varp);
        }
    }
};

std::unique_ptr<DfgGraph> V3DfgPasses::astToDfg(AstModule& module, V3DfgContext& ctx) {
    DfgGraph* const dfgp = new DfgGraph{&module, module.name()};
    AstToDfgVisitor</* T_Scoped: */ false>::apply(*dfgp, module, ctx.m_ast2DfgContext);
    return std::unique_ptr<DfgGraph>{dfgp};
}

std::unique_ptr<DfgGraph> V3DfgPasses::astToDfg(AstNetlist& netlist, V3DfgContext& ctx) {
    DfgGraph* const dfgp = new DfgGraph{nullptr, "netlist"};
    AstToDfgVisitor</* T_Scoped: */ true>::apply(*dfgp, netlist, ctx.m_ast2DfgContext);
    return std::unique_ptr<DfgGraph>{dfgp};
}
