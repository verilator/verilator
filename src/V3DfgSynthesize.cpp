// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgLogic into primitive operations
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
// Synthesize DfgLogic vertices in as a graph, as created by V3DfgAstToDfg
// into primitive vertices.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Cfg.h"
#include "V3Const.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3EmitV.h"
#include "V3Os.h"

#include <algorithm>
#include <iterator>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create a DfgVertex out of a AstNodeExpr. For most AstNodeExpr subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename T_Vertex, typename T_Node>
T_Vertex* makeVertex(const T_Node* nodep, DfgGraph& dfg, const DfgDataType& dtype) {
    return new T_Vertex{dfg, nodep->fileline(), dtype};
}

template <>
DfgArraySel* makeVertex<DfgArraySel, AstArraySel>(const AstArraySel* nodep, DfgGraph& dfg,
                                                  const DfgDataType& dtype) {
    // Some earlier passes create malformed ArraySels, just bail on those...
    // See t_bitsel_wire_array_bad
    if (VN_IS(nodep->fromp(), Const)) return nullptr;
    if (!VN_IS(nodep->fromp()->dtypep()->skipRefp(), UnpackArrayDType)) return nullptr;
    return new DfgArraySel{dfg, nodep->fileline(), dtype};
}

}  // namespace

// Visitor that can convert Ast statements and expressions in Dfg vertices
template <bool T_Scoped>
class AstToDfgConverter final : public VNVisitor {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node
    // AstVar::user3()                        -> int temporary counter for variable
    const VNUser3InUse m_user3InUse;

    // TYPES
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // STATE
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats

    // Current logic vertex we are synthesizing
    DfgLogic* m_logicp = nullptr;
    // Variable updates produced by currently converted statement. This almost
    // always have a single element, so a vector is ok
    std::vector<std::pair<Variable*, DfgVertexVar*>>* m_updatesp = nullptr;

    bool m_foundUnhandled = false;  // Found node not implemented as DFG or not implemented 'visit'
    bool m_converting = false;  // We are trying to convert some logic at the moment

    size_t m_nUnpack = 0;  // Sequence numbers for temporaries

    // METHODS
    static Variable* getTarget(const AstVarRef* refp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(refp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(refp->varp());
        }
    }

    // Allocate a new non-variable vertex, add it to the currently synthesized logic
    template <typename Vertex, typename... Args>
    Vertex* make(Args&&... args) {
        static_assert(!std::is_base_of<DfgVertexVar, Vertex>::value, "Do not use for variables");
        static_assert(std::is_base_of<DfgVertex, Vertex>::value, "'Vertex' must be a 'DfgVertex'");
        Vertex* const vtxp = new Vertex{m_dfg, std::forward<Args>(args)...};
        m_logicp->synth().emplace_back(vtxp);
        return vtxp;
    }

    // Returns true if the expression cannot (or should not) be represented by DFG
    bool unhandled(AstNodeExpr* nodep) {
        // Short-circuiting if something was already unhandled
        if (m_foundUnhandled) {
            // Impure nodes cannot be represented
            if (!nodep->isPure()) {
                m_foundUnhandled = true;
                ++m_ctx.m_conv.nonRepImpure;
            }
        }
        return m_foundUnhandled;
    }

    bool isSupported(const AstVarRef* nodep) {
        // Cannot represent cross module references
        if (nodep->classOrPackagep()) return false;
        // Check target
        return V3Dfg::isSupported(getTarget(nodep));
    }

    // Given an RValue expression, return the equivalent Vertex, or nullptr if not representable.
    DfgVertex* convertRValue(AstNodeExpr* nodep) {
        UASSERT_OBJ(!m_converting, nodep, "'convertingRValue' should not be called recursively");
        VL_RESTORER(m_converting);
        VL_RESTORER(m_foundUnhandled);
        m_converting = true;
        m_foundUnhandled = false;

        // Convert the expression
        iterate(nodep);

        // If falied to convert, return nullptr
        if (m_foundUnhandled) return nullptr;

        // Traversal set user2p to the equivalent vertex
        DfgVertex* const vtxp = nodep->user2u().to<DfgVertex*>();
        UASSERT_OBJ(vtxp, nodep, "Missing Dfg vertex after conversion");
        return vtxp;
    }

    // Given an LValue expression, return the splice node that writes the
    // destination, together with the index to use for splicing in the value.
    // Returns {nullptr, 0}, if the given LValue expression is not supported.
    std::pair<DfgVertexSplice*, uint32_t> convertLValue(AstNodeExpr* nodep) {
        if (const AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            if (!isSupported(vrefp)) {
                ++m_ctx.m_conv.nonRepLValue;
                return {nullptr, 0};
            }

            // Get (or create a new) temporary for this variable
            const DfgVertexVar* const vtxp = [&]() -> DfgVertexVar* {
                // The variable being assigned
                Variable* const tgtp = getTarget(vrefp);

                // Find existing one, if any
                for (const auto& pair : *m_updatesp) {
                    if (pair.first == tgtp) return pair.second;
                }

                // Create new one
                DfgVertexVar* const newp = createTmp(*m_logicp, tgtp, "SynthAssign");
                m_updatesp->emplace_back(tgtp, newp);

                // Create the Splice driver for the new temporary
                if (newp->is<DfgVarPacked>()) {
                    newp->srcp(make<DfgSplicePacked>(newp->fileline(), newp->dtype()));
                } else if (newp->is<DfgVarArray>()) {
                    newp->srcp(make<DfgSpliceArray>(newp->fileline(), newp->dtype()));
                } else {
                    nodep->v3fatalSrc("Unhandled DfgVertexVar sub-type");
                }

                // Use new temporary
                return newp;
            }();

            // Return the Splice driver
            return {vtxp->srcp()->as<DfgVertexSplice>(), 0};
        }

        if (const AstSel* selp = VN_CAST(nodep, Sel)) {
            // Only handle constant selects
            const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
            if (!lsbp) {
                ++m_ctx.m_conv.nonRepLValue;
                return {nullptr, 0};
            }
            uint32_t lsb = lsbp->toUInt();

            // Convert the 'fromp' sub-expression
            const auto pair = convertLValue(selp->fromp());
            if (!pair.first) return {nullptr, 0};
            DfgSplicePacked* const splicep = pair.first->template as<DfgSplicePacked>();
            // Adjust index.
            lsb += pair.second;

            // Don't optimize if statically out of bounds. TODO: Maybe later ...
            if (lsb + static_cast<uint32_t>(selp->widthConst()) > splicep->size()) {
                ++m_ctx.m_conv.nonRepOOBSel;
                return {nullptr, 0};
            }

            // AstSel doesn't change type kind (array vs packed), so we can use
            // the existing splice driver with adjusted lsb
            return {splicep, lsb};
        }

        if (const AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
            // Only handle constant selects
            const AstConst* const indexp = VN_CAST(aselp->bitp(), Const);
            if (!indexp) {
                ++m_ctx.m_conv.nonRepLValue;
                return {nullptr, 0};
            }
            uint32_t index = indexp->toUInt();

            // Convert the 'fromp' sub-expression
            const auto pair = convertLValue(aselp->fromp());
            if (!pair.first) return {nullptr, 0};
            DfgSpliceArray* const splicep = pair.first->template as<DfgSpliceArray>();
            // Adjust index. Note pair.second is always 0, but we might handle array slices later..
            index += pair.second;

            // Don't optimize if statically out of bounds. TODO: Maybe later ...
            if (index + 1U > splicep->size()) {
                ++m_ctx.m_conv.nonRepOOBSel;
                return {nullptr, 0};
            }

            // Ensure the Splice driver exists for this element
            if (!splicep->driverAt(index)) {
                FileLine* const flp = nodep->fileline();
                // This should never fail
                const DfgDataType& dtype = *DfgDataType::fromAst(nodep->dtypep());
                if (dtype.isPacked()) {
                    DfgSplicePacked* const newp = make<DfgSplicePacked>(flp, dtype);
                    const DfgDataType& uaDtype = DfgDataType::array(dtype, 1);
                    DfgUnitArray* const uap = make<DfgUnitArray>(flp, uaDtype);
                    uap->srcp(newp);
                    splicep->addDriver(uap, index, flp);
                } else if (dtype.isArray()) {
                    DfgSpliceArray* const newp = make<DfgSpliceArray>(flp, dtype);
                    splicep->addDriver(newp, index, flp);
                } else {
                    nodep->v3fatalSrc("Unhandled data type kind");
                }
            }

            // Return the splice driver
            DfgVertex* driverp = splicep->driverAt(index);
            if (const DfgUnitArray* const uap = driverp->cast<DfgUnitArray>()) {
                driverp = uap->srcp();
            }
            return {driverp->as<DfgVertexSplice>(), 0};
        }

        ++m_ctx.m_conv.nonRepLValue;
        return {nullptr, 0};
    }

    // Given the LHS of an assignment, and the vertex representing the RHS,
    // connect up the RHS to drive the targets.
    // Returns true on success, false if the LHS is not representable.
    bool convertAssignment(FileLine* flp, AstNodeExpr* lhsp, DfgVertex* vtxp) {
        // Represents a DFG assignment contributed by the AST assignment with the above 'lhsp'.
        // There might be multiple of these if 'lhsp' is a concatenation.
        struct Assignment final {
            DfgVertexSplice* m_lhsp;
            uint32_t m_idx;
            DfgVertex* m_rhsp;
            Assignment() = delete;
            Assignment(DfgVertexSplice* lhsp, uint32_t idx, DfgVertex* rhsp)
                : m_lhsp{lhsp}
                , m_idx{idx}
                , m_rhsp{rhsp} {}
        };

        // Simplify the LHS, to get rid of things like SEL(CONCAT(_, _), _)
        lhsp = VN_AS(V3Const::constifyExpensiveEdit(lhsp), NodeExpr);

        // Assigning compound expressions to a concatenated LHS requires a temporary
        // to avoid multiple use of the expression
        if (VN_IS(lhsp, Concat) && !vtxp->is<DfgVertexVar>() && !vtxp->is<DfgConst>()) {
            const size_t n = ++m_nUnpack;
            DfgVertexVar* const tmpp = createTmp(*m_logicp, flp, vtxp->dtype(), "Unpack", n);
            tmpp->srcp(vtxp);
            vtxp = tmpp;
        }

        // Convert each concatenation LHS separately, gather all assignments
        // we need to do into 'assignments', return true if all LValues
        // converted successfully.
        std::vector<Assignment> assignments;
        const std::function<bool(AstNodeExpr*, uint32_t)> convertAllLValues
            = [&](AstNodeExpr* subp, uint32_t lsb) -> bool {
            // Concatenation on the LHS, convert each part
            if (AstConcat* const concatp = VN_CAST(subp, Concat)) {
                AstNodeExpr* const cRhsp = concatp->rhsp();
                AstNodeExpr* const cLhsp = concatp->lhsp();
                // Convert Rigth of concat
                if (!convertAllLValues(cRhsp, lsb)) return false;
                // Convert Left of concat
                return convertAllLValues(cLhsp, lsb + cRhsp->width());
            }

            // Non-concatenation, convert the LValue
            const auto pair = convertLValue(subp);
            if (!pair.first) return false;

            // If whole lhs, just use it
            if (subp == lhsp) {
                assignments.emplace_back(pair.first, pair.second, vtxp);
                return true;
            }

            // Otherwise select the relevant bits
            const DfgDataType& dtype = *DfgDataType::fromAst(subp->dtypep());
            DfgSel* const selp = make<DfgSel>(subp->fileline(), dtype);
            selp->fromp(vtxp);
            selp->lsb(lsb);
            assignments.emplace_back(pair.first, pair.second, selp);
            return true;
        };

        // Convert the given LHS assignment, give up if any LValues failed to convert
        if (!convertAllLValues(lhsp, 0)) return false;

        // All successful, connect the drivers
        for (const Assignment& item : assignments) {
            if (DfgSplicePacked* const spp = item.m_lhsp->template cast<DfgSplicePacked>()) {
                spp->addDriver(item.m_rhsp, item.m_idx, flp);
            } else if (DfgSpliceArray* const sap = item.m_lhsp->template cast<DfgSpliceArray>()) {
                // TODO: multi-dimensional arrays will need changes here
                const DfgDataType& rDt = item.m_rhsp->dtype();
                if (rDt.isPacked()) {
                    // RHS is assigning an element of this array. Need a DfgUnitArray adapter.
                    DfgUnitArray* const uap = make<DfgUnitArray>(flp, DfgDataType::array(rDt, 1));
                    uap->srcp(item.m_rhsp);
                    sap->addDriver(uap, item.m_idx, flp);
                } else {
                    // RHS is assigning an array (or array slice). Should be the same element type.
                    sap->addDriver(item.m_rhsp, item.m_idx, flp);
                }
            } else {
                item.m_lhsp->v3fatalSrc("Unhandled DfgVertexSplice sub-type");
            }
        }

        return true;
    }

    // VISITORS

    // Unhandled node
    void visit(AstNode* nodep) override {
        if (!m_foundUnhandled && m_converting) ++m_ctx.m_conv.nonRepUnknown;
        m_foundUnhandled = true;
    }

    // Expressions - mostly auto generated, but a few special ones
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        // This visit method is only called on RValues, where only read refs are supported
        if (!nodep->access().isReadOnly() || !isSupported(nodep)) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepVarRef;
            return;
        }

        // Variable should have been bound before starting conversion
        DfgVertex* const vtxp = getTarget(nodep)->user2u().template to<DfgVertexVar*>();
        UASSERT_OBJ(vtxp, nodep, "Referenced variable has no associated DfgVertexVar");
        nodep->user2p(vtxp);
    }
    void visit(AstConst* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        if (nodep->width() != nodep->num().width()) {
            // Sometimes the width of the AstConst is not the same as the
            // V3Number it holds. Truncate it here. TODO: should this be allowed?
            V3Number num{nodep, nodep->width()};
            num.opSel(nodep->num(), nodep->width() - 1, 0);
            DfgVertex* const vtxp = make<DfgConst>(nodep->fileline(), num);
            nodep->user2p(vtxp);
        } else {
            DfgVertex* const vtxp = make<DfgConst>(nodep->fileline(), nodep->num());
            nodep->user2p(vtxp);
        }
    }
    void visit(AstSel* nodep) override {
        UASSERT_OBJ(m_converting, nodep, "AstToDfg visit called without m_converting");
        UASSERT_OBJ(!nodep->user2p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        const DfgDataType* const dtypep = DfgDataType::fromAst(nodep->dtypep());
        if (!dtypep) {
            m_foundUnhandled = true;
            ++m_ctx.m_conv.nonRepDType;
            return;
        }

        iterate(nodep->fromp());
        if (m_foundUnhandled) return;

        FileLine* const flp = nodep->fileline();
        DfgVertex* vtxp = nullptr;
        if (const AstConst* const constp = VN_CAST(nodep->lsbp(), Const)) {
            const uint32_t lsb = constp->toUInt();
            const uint32_t msb = lsb + nodep->widthConst() - 1;
            DfgVertex* const fromp = nodep->fromp()->user2u().to<DfgVertex*>();
            // Unfortunately we can still have out of bounds selects due to how
            // indices are truncated for speed reasons in V3Width/V3Unknown.
            if (msb >= fromp->size()) {
                m_foundUnhandled = true;
                ++m_ctx.m_conv.nonRepOOBSel;
                return;
            }
            DfgSel* const selp = make<DfgSel>(flp, *dtypep);
            selp->fromp(fromp);
            selp->lsb(lsb);
            vtxp = selp;
        } else {
            iterate(nodep->lsbp());
            if (m_foundUnhandled) return;
            DfgMux* const muxp = make<DfgMux>(flp, *dtypep);
            muxp->fromp(nodep->fromp()->user2u().to<DfgVertex*>());
            muxp->lsbp(nodep->lsbp()->user2u().to<DfgVertex*>());
            vtxp = muxp;
        }
        nodep->user2p(vtxp);
    }
// The rest of the visit methods for expressions are generated by 'astgen'
#include "V3Dfg__gen_ast_to_dfg.h"

public:
    // PUBLIC METHODS

    // Create temporay variable capable of holding the given type
    DfgVertexVar* createTmp(DfgLogic& logic, FileLine* flp, const DfgDataType& dtype,
                            const std::string& prefix, size_t tmpCount) {
        const std::string name = m_dfg.makeUniqueName(prefix, tmpCount);
        DfgVertexVar* const vtxp = m_dfg.makeNewVar(flp, name, dtype, logic.scopep());
        logic.synth().emplace_back(vtxp);
        vtxp->varp()->isInternal(true);
        vtxp->tmpForp(vtxp->nodep());
        return vtxp;
    }

    // Create a new temporary variable capable of holding 'varp'
    DfgVertexVar* createTmp(DfgLogic& logic, Variable* varp, const std::string& prefix) {
        AstVar* const astVarp = T_Scoped ? reinterpret_cast<AstVarScope*>(varp)->varp()
                                         : reinterpret_cast<AstVar*>(varp);
        FileLine* const flp = astVarp->fileline();
        const DfgDataType& dtype = *DfgDataType::fromAst(astVarp->dtypep());
        const std::string prfx = prefix + "_" + astVarp->name();
        const size_t tmpCount = astVarp->user3Inc();
        DfgVertexVar* const vtxp = createTmp(logic, flp, dtype, prfx, tmpCount);
        vtxp->tmpForp(varp);
        return vtxp;
    }

    // Convert AstAssign to Dfg, return true if successful.
    // Fills 'updates' with bindings for assigned variables.
    bool convert(std::vector<std::pair<Variable*, DfgVertexVar*>>& updates, DfgLogic& vtx,
                 AstAssign* nodep) {
        UASSERT_OBJ(updates.empty(), nodep, "'updates' should be empty");
        VL_RESTORER(m_updatesp);
        VL_RESTORER(m_logicp);
        m_updatesp = &updates;
        m_logicp = &vtx;
        // Assignment with timing control shouldn't make it this far
        UASSERT_OBJ(!nodep->timingControlp(), nodep, "Shouldn't make it this far");
        // Convert it
        ++m_ctx.m_conv.inputAssignments;
        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();
        // Check data types are compatible.
        const DfgDataType* const lDtypep = DfgDataType::fromAst(lhsp->dtypep());
        const DfgDataType* const rDtypep = DfgDataType::fromAst(rhsp->dtypep());
        if (!lDtypep || !rDtypep) {
            ++m_ctx.m_conv.nonRepDType;
            return false;
        }
        // For now, only direct array assignment is supported (e.g. a = b, but not a = _ ? b : c)
        if (rDtypep->isArray() && !VN_IS(rhsp, VarRef)) {
            ++m_ctx.m_conv.nonRepDType;
            return false;
        }
        // Widths should match at this point
        UASSERT_OBJ(lhsp->width() == rhsp->width(), nodep, "Mismatched width reached DFG");
        // Convert the RHS expression
        DfgVertex* const rVtxp = convertRValue(rhsp);
        if (!rVtxp) return false;
        // Connect the RHS vertex to the LHS targets
        const bool success = convertAssignment(nodep->fileline(), lhsp, rVtxp);
        if (success) ++m_ctx.m_conv.representable;
        return success;
    }

    // Convert RValue expression to Dfg. Returns nullptr if failed.
    DfgVertex* convert(DfgLogic& vtx, AstNodeExpr* nodep) {
        VL_RESTORER(m_logicp);
        m_logicp = &vtx;
        // Convert it
        ++m_ctx.m_conv.inputExpressions;
        DfgVertex* const vtxp = convertRValue(nodep);
        if (vtxp) ++m_ctx.m_conv.representable;
        return vtxp;
    }

    // CONSTRUCTOR
    AstToDfgConverter(DfgGraph& dfg, V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {}
};

// For debugging, we can stop synthesizing after a certain number of vertices.
// for this we need a global counter (inside the template makes multiple copies)
static size_t s_dfgSynthDebugCount = 0;
// The number of vertices we stop after can be passed in through the environment
// you can then use a bisection search over this value and look at the dumps
// produced with the lowest failing value
static const size_t s_dfgSynthDebugLimit
    = std::stoull(V3Os::getenvStr("VERILATOR_DFG_SYNTH_DEBUG", "0"));

template <bool T_Scoped>
class AstToDfgSynthesize final {
    // NODE STATE
    // AstNodeExpr/AstVar/AstVarScope::user2p -> DfgVertex* for this Node

    // TYPES
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;

    // SymTab must be ordered in order to yield stable results
    struct VariableComparator final {
        bool operator()(const Variable* lhs, const Variable* rhs) const {
            return lhs->name() < rhs->name();
        }
    };
    using SymTab = std::map<Variable*, DfgVertexVar*, VariableComparator>;

    // Represents a [potentially partial] driver of a variable
    struct Driver final {
        DfgVertex* m_vtxp = nullptr;  // Driving vertex
        uint32_t m_lo = 0;  // Low index of driven range (internal, not Verilog)
        uint32_t m_hi = 0;  // High index of driven range (internal, not Verilog)
        FileLine* m_flp = nullptr;  // Location of driver in source

        Driver() = default;
        Driver(DfgVertex* vtxp, uint32_t lo, FileLine* flp)
            : m_vtxp{vtxp}
            , m_lo{lo}
            , m_hi{lo + vtxp->size() - 1U}
            , m_flp{flp} {}
        operator bool() const { return m_vtxp != nullptr; }

        bool operator<(const Driver& other) const {
            if (m_lo != other.m_lo) return m_lo < other.m_lo;
            if (m_hi != other.m_hi) return m_hi < other.m_hi;
            return m_flp->operatorCompare(*other.m_flp) < 0;
        }

        bool operator<=(const Driver& other) const { return !(other < *this); }
    };

    // STATE - Persistent
    DfgGraph& m_dfg;  // The graph being built
    V3DfgSynthesisContext& m_ctx;  // The context for stats
    AstToDfgConverter<T_Scoped> m_converter;  // The convert instance to use for each construct
    size_t m_nBranchCond = 0;  // Sequence numbers for temporaries
    size_t m_nPathPred = 0;  // Sequence numbers for temporaries
    DfgWorklist m_toRevert{m_dfg};  // We need a worklist for reverting synthesis

    // STATE - for current DfgLogic being synthesized
    DfgLogic* m_logicp = nullptr;  // Current logic vertex we are synthesizing
    CfgBlockMap<SymTab> m_bbToISymTab;  // Map from CfgBlock -> input symbol table
    CfgBlockMap<SymTab> m_bbToOSymTab;  // Map from CfgBlock -> output symbol table
    CfgBlockMap<DfgVertexVar*> m_bbToCondp;  // Map from CfgBlock ->  terminating branch condition
    CfgEdgeMap<DfgVertexVar*> m_edgeToPredicatep;  // Map CfgGraphEdge -> path predicate to there
    CfgDominatorTree m_domTree;  // The dominator tree of the current CFG

    // STATE - Some debug aid
    // We stop after synthesizing s_dfgSynthDebugLimit vertices (if non-zero).
    // This is the problematic logic (last one we synthesize), assuming a
    // bisection search over s_dfgSynthDebugLimit.
    DfgLogic* m_debugLogicp = nullptr;
    // Source (upstream) cone of outputs of m_debugLogicp
    std::unique_ptr<std::unordered_set<const DfgVertex*>> m_debugOSrcConep{nullptr};

    // METHODS

    // Dump current graph for debugging ...
    void debugDump(const char* name) {
        // If we have the debugged logic, compute the vertices feeding its outputs
        if (VL_UNLIKELY(m_debugLogicp)) {
            std::vector<const DfgVertex*> outputs;
            m_debugLogicp->foreachSink([&outputs](const DfgVertex& v) {
                outputs.emplace_back(v.singleSink()->as<DfgVertexVar>());
                return false;
            });
            m_debugOSrcConep = m_dfg.sourceCone(outputs);
        }

        if (VL_UNLIKELY(dumpDfgLevel() >= 9 || m_debugOSrcConep)) {
            const auto label = m_ctx.prefix() + name;
            m_dfg.dumpDotFilePrefixed(label);
            if (m_debugOSrcConep) {
                // Dump only the subgraph involving the inputs and outputs of the bad vertex
                m_dfg.dumpDotFilePrefixed(label + "-min", [&](const DfgVertex& v) -> bool {
                    return m_debugOSrcConep->count(&v);
                });
            }
        }
    }

    static AstVar* getAstVar(Variable* vp) {
        // TODO: remove the useless reinterpret_casts when C++17 'if constexpr' actually works
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<AstVarScope*>(vp)->varp();
        } else {
            return reinterpret_cast<AstVar*>(vp);
        }
    }

    // Allocate a new non-variable vertex, add it to the currently synthesized logic
    template <typename Vertex, typename... Args>
    Vertex* make(Args&&... args) {
        static_assert(!std::is_base_of<DfgVertexVar, Vertex>::value, "Do not use for variables");
        static_assert(std::is_base_of<DfgVertex, Vertex>::value, "'Vertex' must be a 'DfgVertex'");
        Vertex* const vtxp = new Vertex{m_dfg, std::forward<Args>(args)...};
        if (m_logicp) m_logicp->synth().emplace_back(vtxp);
        return vtxp;
    }

    // Gather all drivers of a resolved variable
    static std::vector<Driver> gatherDrivers(DfgVertexSplice* vtxp) {
        // Collect them all, check if they are sorted
        std::vector<Driver> drivers;
        drivers.reserve(vtxp->nInputs());
        bool sorted = true;
        vtxp->foreachDriver([&](DfgVertex& src, uint32_t lo, FileLine* flp) {
            // Collect the driver
            drivers.emplace_back(&src, lo, flp);
            // Check if drivers are sorted - most often they are
            const size_t n = drivers.size();
            if (n >= 2 && drivers[n - 1] < drivers[n - 2]) sorted = false;
            return false;
        });

        // Sort if unsorted
        if (!sorted) std::stable_sort(drivers.begin(), drivers.end());

        // Done
        return drivers;
    }

    // Gather all synthesized drivers of an unresolved variable
    static std::vector<Driver> gatherDriversUnresolved(DfgUnresolved* vtxp) {
        std::vector<Driver> drivers;
        drivers.reserve(vtxp->nInputs());

        // For better locations in error reporting, we unpick concatenations
        // which are sometimes introduced by combinint assignments in V3Const.
        const std::function<void(DfgVertex*, uint32_t, FileLine*)> gather
            = [&](DfgVertex* vtxp, uint32_t lo, FileLine* flp) -> void {
            if (DfgConcat* const concatp = vtxp->cast<DfgConcat>()) {
                DfgVertex* const rhsp = concatp->rhsp();
                gather(rhsp, lo, rhsp->fileline());
                DfgVertex* const lhsp = concatp->lhsp();
                gather(lhsp, lo + rhsp->width(), lhsp->fileline());
                return;
            }
            drivers.emplace_back(vtxp, lo, flp);
        };

        // Gather all synthesized drivers
        vtxp->foreachSource([&](DfgVertex& src) {
            // Can ignore the original DfgLogic
            if (src.is<DfgLogic>()) return false;
            // Synthesized drivers must be a splice at this point
            DfgVertexSplice* const splicep = src.as<DfgVertexSplice>();
            // Collect the driver
            splicep->foreachDriver([&](DfgVertex& src, uint32_t lo, FileLine* flp) {
                gather(&src, lo, flp);
                return false;
            });
            return false;
        });

        // Sort the drivers
        std::stable_sort(drivers.begin(), drivers.end());

        // Done
        return drivers;
    }

    // Given two drivers, combine the driven sub-ranges into the first one if
    // possible. First bool returned indicates successfully combined and there
    // are no multi-driven bits. Second bool returned indicates we warned
    // already about multi-driven bits.
    std::pair<bool, bool> combineDrivers(DfgVertexVar& var, const std::string& sub,  //
                                         Driver& a, const Driver& b) {
        // We can only combine array drivers ...
        if (a.m_vtxp->isPacked()) return {false, false};
        // ... that both drive a single element ...
        if (a.m_lo != b.m_lo) return {false, false};
        const DfgUnitArray* const aUap = a.m_vtxp->template cast<DfgUnitArray>();
        if (!aUap) return {false, false};
        const DfgUnitArray* const bUap = b.m_vtxp->template cast<DfgUnitArray>();
        if (!bUap) return {false, false};
        // ... and are themeselves partial
        DfgSplicePacked* const aSp = aUap->srcp()->template cast<DfgSplicePacked>();
        if (!aSp) return {false, false};
        DfgSplicePacked* const bSp = bUap->srcp()->template cast<DfgSplicePacked>();
        if (!bSp) return {false, false};
        UASSERT_OBJ(aSp->dtype() == bSp->dtype(), &var, "DTypes should match");

        // Gather drivers of a
        std::vector<Driver> aDrivers = gatherDrivers(aSp);
        // Gather drivers of b
        std::vector<Driver> bDrivers = gatherDrivers(bSp);

        // Merge them
        std::vector<Driver> abDrivers;
        abDrivers.reserve(aDrivers.size() + bDrivers.size());
        std::merge(  //
            aDrivers.begin(), aDrivers.end(),  //
            bDrivers.begin(), bDrivers.end(),  //
            std::back_inserter(abDrivers)  //
        );

        // Attempt to resolve them
        if (!normalizeDrivers(var, abDrivers, sub + "[" + std::to_string(a.m_lo) + "]")) {
            return {false, true};
        }

        // Successfully resolved. Needs a new splice and unit.
        FileLine* const flp = var.fileline();
        DfgSplicePacked* const splicep = make<DfgSplicePacked>(flp, aSp->dtype());
        for (const Driver& d : abDrivers) splicep->addDriver(d.m_vtxp, d.m_lo, d.m_flp);
        DfgUnitArray* const uap = make<DfgUnitArray>(flp, aUap->dtype());
        uap->srcp(splicep);
        a.m_vtxp = uap;
        return {true, false};
    }

    // Combine and coalesce the given drivers.
    // Returns true iff no multi-driven bits are present.
    bool normalizeDrivers(DfgVertexVar& var, std::vector<Driver>& drivers,
                          const std::string& sub = "") {
        if (drivers.empty()) return true;

        // What type of values are we combining
        const bool isPacked = drivers[0].m_vtxp->isPacked();

        // Found a multidriven part ?
        bool multiDriven = false;

        // Iterate through the sorted drivers. Index 'i' is the driver we are
        // resolving driver 'j' agains, and if required, we merge 'j' into 'i'.
        size_t i = 0;
        for (size_t j = 1; j < drivers.size();) {
            UASSERT_OBJ(i < j, &var, "Invalid iteration");
            Driver& iD = drivers[i];
            Driver& jD = drivers[j];

            // If 'j' was moved, step forward
            if (!jD) {
                ++j;
                continue;
            }
            // If 'i' was moved, move 'j' in it's place
            if (!iD) {
                iD = jD;
                jD = Driver{};
                ++j;
                continue;
            }

            // We have 2 valid drivers now
            UASSERT_OBJ(iD <= jD, &var, "Should always be sorted");
            UASSERT_OBJ(jD.m_vtxp->isPacked() == isPacked, &var, "Mixed type drivers");

            // If no overlap, consider next pair
            if (iD.m_hi < jD.m_lo) {
                ++i;
                if (i == j) ++j;
                continue;
            }

            // There is an overlap. Attempt to combine them.
            bool combined = false;
            bool warned = false;
            std::tie(combined, warned) = combineDrivers(var, sub, iD, jD);

            // If sucessfully combined, 'j' is no longer needed, it was combined into 'i'
            if (combined) {
                jD = Driver{};
                ++j;
                continue;
            }

            // Found overlap that cannot be resolved
            multiDriven = true;
            // Compare next driver
            ++j;

            // Do not warn again if we warned during 'combineDrivers'
            if (warned) continue;

            // The variable to warn on
            AstNode* const nodep = var.tmpForp() ? var.tmpForp() : var.nodep();
            Variable* const varp = reinterpret_cast<Variable*>(nodep);

            // Loop index often abused, so suppress
            if (getAstVar(varp)->isUsedLoopIdx()) continue;

            // Warn the user now
            const std::string lo = std::to_string(jD.m_lo);
            const std::string hi = std::to_string(std::min(iD.m_hi, jD.m_hi));
            const std::string kind = isPacked ? "Bit" : "Element";
            const std::string part = hi == lo ? (" [" + lo + "]") : ("s [" + hi + ":" + lo + "]");

            varp->v3warn(  //
                MULTIDRIVEN,  //
                kind << part << " of signal '" << varp->prettyName() << sub << "'"
                     << " have multiple combinational drivers."
                     << " This can cause performance degradation.\n"
                     << iD.m_flp->warnOther() << "... Location of offending driver\n"
                     << iD.m_flp->warnContextPrimary() << '\n'
                     << jD.m_flp->warnOther() << "... Location of offending driver\n"
                     << jD.m_flp->warnContextSecondary());
        }
        // Rightsize vector
        drivers.resize(i + 1);

        // Coalesce adjacent drivers
        if (!multiDriven && isPacked) coalesceDrivers(drivers);

        return !multiDriven;
    }

    // Coalesce adjacent drivers into single ones
    void coalesceDrivers(std::vector<Driver>& drivers) {
        UASSERT(!drivers.empty(), "Can't coalesce 0 drivers");
        UASSERT_OBJ(drivers[0].m_vtxp->isPacked(), drivers[0].m_vtxp, "Can only coalesce packed");

        size_t i = 0;
        for (size_t j = 1; j < drivers.size();) {
            UASSERT(i < j, "Invalid iteration");
            Driver& iD = drivers[i];
            Driver& jD = drivers[j];

            // If 'j' was moved, step forward
            if (!jD) {
                ++j;
                continue;
            }
            // If 'i' was moved, move 'j' in it's place
            if (!iD) {
                iD = jD;
                jD = Driver{};
                ++j;
                continue;
            }

            // We have 2 valid drivers now
            UASSERT(iD <= jD, "Should always be sorted");

            // If not adjacent, move on
            if (iD.m_hi + 1 != jD.m_lo) {
                ++i;
                if (i == j) ++j;
                continue;
            }

            // Coalesce Adjacent ranges,
            const DfgDataType& dt = DfgDataType::packed(iD.m_vtxp->width() + jD.m_vtxp->width());
            DfgConcat* const concatp = make<DfgConcat>(iD.m_flp, dt);
            concatp->rhsp(iD.m_vtxp);
            concatp->lhsp(jD.m_vtxp);
            iD.m_vtxp = concatp;
            iD.m_hi = jD.m_hi;
            jD = Driver{};

            // Consider next driver
            ++j;
        }
        // Rightsize vector
        drivers.resize(i + 1);
    }

    // Make a new splice with the given drivers
    DfgVertexSplice* makeSplice(DfgVertexVar& var, const std::vector<Driver>& newDrivers) {
        UASSERT_OBJ(!newDrivers.empty(), &var, "'makeSplice' called with no new drivers");
        // Create new driver
        DfgVertexSplice* splicep = nullptr;
        if (var.is<DfgVarPacked>()) {
            splicep = make<DfgSplicePacked>(var.fileline(), var.dtype());
        } else if (var.is<DfgVarArray>()) {
            splicep = make<DfgSpliceArray>(var.fileline(), var.dtype());
        } else {
            var.v3fatalSrc("Unhandled DfgVertexVar sub-type");
        }
        for (const Driver& d : newDrivers) splicep->addDriver(d.m_vtxp, d.m_lo, d.m_flp);
        return splicep;
    }

    // Initialzie input symbol table of entry CfgBlock
    void initializeEntrySymbolTable(SymTab& iSymTab) {
        m_logicp->foreachSource([&](DfgVertex& src) {
            DfgVertexVar* const vvp = src.as<DfgVertexVar>();
            Variable* const varp = reinterpret_cast<Variable*>(vvp->nodep());
            iSymTab[varp] = vvp;
            return false;
        });
    }

    // Join variable drivers across a control flow confluence (insert muxes ...)
    DfgVertexVar* joinDrivers(Variable* varp, DfgVertexVar* predicatep,  //
                              DfgVertexVar* thenp, DfgVertexVar* elsep) {
        AstNode* const thenVarp = thenp->tmpForp() ? thenp->tmpForp() : thenp->nodep();
        AstNode* const elseVarp = elsep->tmpForp() ? elsep->tmpForp() : elsep->nodep();
        UASSERT_OBJ(thenVarp == elseVarp, varp, "Attempting to join unrelated variables");

        // If both bindings are the the same (variable not updated through either path),
        // then there is nothing to do, can use the same binding
        if (thenp == elsep) return thenp;

        // We can't join the input variable just yet, so bail
        if (thenp->nodep() == varp) {
            ++m_ctx.m_synt.nonSynJoinInput;
            return nullptr;
        }
        if (elsep->nodep() == varp) {
            ++m_ctx.m_synt.nonSynJoinInput;
            return nullptr;
        }

        // Can't do arrays yet
        if (!thenp->isPacked()) {
            ++m_ctx.m_synt.nonSynArray;
            return nullptr;
        }

        // Gather drivers of 'thenp' - only if 'thenp' is not an input to the synthesized block
        DfgVertex* const tDefaultp = thenp->defaultp();
        std::vector<Driver> tDrivers = gatherDrivers(thenp->srcp()->as<DfgVertexSplice>());

        // Gather drivers of 'elsep' - only if 'thenp' is not an input to the synthesized block
        DfgVertex* const eDefaultp = elsep->defaultp();
        std::vector<Driver> eDrivers = gatherDrivers(elsep->srcp()->as<DfgVertexSplice>());

        // Default drivers should be the same or not present on either
        UASSERT_OBJ(tDefaultp == eDefaultp, varp, "Different default drivers");

        // Location to use for the join vertices
        FileLine* const flp = predicatep->fileline();

        // Create a fresh temporary for the joined value
        DfgVertexVar* const joinp = m_converter.createTmp(*m_logicp, varp, "SynthJoin");
        DfgVertexSplice* const joinSplicep = make<DfgSplicePacked>(flp, joinp->dtype());
        joinp->srcp(joinSplicep);

        // If both paths are fully driven, just create a simple conditional
        if (tDrivers.size() == 1  //
            && tDrivers[0].m_lo == 0  //
            && tDrivers[0].m_hi == thenp->width() - 1  //
            && eDrivers.size() == 1  //
            && eDrivers[0].m_lo == 0  //
            && eDrivers[0].m_hi == elsep->width() - 1) {
            UASSERT_OBJ(!tDefaultp, varp, "Fully driven variable have default driver");

            DfgCond* const condp = make<DfgCond>(flp, joinp->dtype());
            condp->condp(predicatep);
            condp->thenp(thenp);
            condp->elsep(elsep);
            joinSplicep->addDriver(condp, 0, tDrivers[0].m_flp);

            // Done
            return joinp;
        }

        // Otherwise we need to merge them part by part

        // If different bits are driven, then some might not have been assigned.. Latch?
        if (tDrivers.size() != eDrivers.size()) {
            ++m_ctx.m_synt.nonSynLatch;
            return nullptr;
        }

        for (size_t i = 0; i < tDrivers.size(); ++i) {
            const Driver& tDriver = tDrivers[i];
            const Driver& eDriver = eDrivers[i];
            // If different bits are driven, then some might not have been assigned.. Latch?
            if (tDriver.m_lo != eDriver.m_lo || tDriver.m_hi != eDriver.m_hi) {
                ++m_ctx.m_synt.nonSynLatch;
                return nullptr;
            }

            const DfgDataType& dtype = DfgDataType::packed(tDriver.m_hi - tDriver.m_lo + 1);
            DfgCond* const condp = make<DfgCond>(flp, dtype);
            condp->condp(predicatep);

            // We actally need to select the bits from the joined variables, not use the drivers
            DfgSel* const thenSelp = make<DfgSel>(flp, tDriver.m_vtxp->dtype());
            thenSelp->lsb(tDriver.m_lo);
            thenSelp->fromp(thenp);
            condp->thenp(thenSelp);

            // Same for the 'else' part
            DfgSel* const elseSelp = make<DfgSel>(flp, eDriver.m_vtxp->dtype());
            elseSelp->lsb(eDriver.m_lo);
            elseSelp->fromp(elsep);
            condp->elsep(elseSelp);

            // Add it as a driver to the join
            joinSplicep->addDriver(condp, tDriver.m_lo, tDriver.m_flp);
        }

        // If there was a default driver, add it to te join
        if (tDefaultp) joinp->defaultp(tDefaultp);

        // Done
        return joinp;
    }

    // Merge 'thenSymTab' into 'elseSymTab' using the given predicate to join values
    bool joinSymbolTables(SymTab& elseSymTab, DfgVertexVar* predicatep, const SymTab& thenSymTab) {
        // Give up if something is not assigned on all paths ... Latch?
        if (thenSymTab.size() != elseSymTab.size()) {
            ++m_ctx.m_synt.nonSynLatch;
            return false;
        }
        // Join each symbol
        for (std::pair<Variable* const, DfgVertexVar*>& pair : elseSymTab) {
            Variable* const varp = pair.first;
            // Find same variable on the else path
            auto it = thenSymTab.find(varp);
            // Give up if something is not assigned on all paths ... Latch?
            if (it == thenSymTab.end()) {
                ++m_ctx.m_synt.nonSynLatch;
                return false;
            }
            // Join paths with the predicate
            DfgVertexVar* const thenp = it->second;
            DfgVertexVar* const elsep = pair.second;
            DfgVertexVar* const newp = joinDrivers(varp, predicatep, thenp, elsep);
            if (!newp) return false;
            pair.second = newp;
        }
        // Done
        return true;
    }

    // Given two joining control flow edges, compute how to join their symbols.
    // Returns the predicaete to join over, and the 'then' and 'else' blocks.
    std::tuple<DfgVertexVar*, const CfgBlock*, const CfgBlock*>  //
    howToJoin(const CfgEdge* const ap, const CfgEdge* const bp) {
        // Find the closest common dominator of the two paths
        const CfgBlock* const domp = m_domTree.closestCommonDominator(ap->srcp(), bp->srcp());
        // These paths join here, so 'domp' must be a branch, otherwise it's not the closest
        UASSERT_OBJ(domp->isBranch(), domp, "closestCommonDominator is not a branch");

        // The branches of the common dominator
        const CfgEdge* const takenEdgep = domp->takenEdgep();
        const CfgEdge* const untknEdgep = domp->untknEdgep();

        // We check if the taken branch dominates the path to either blocks,
        // and if the untaken branch dominates the path to the other block.
        // If so, we can use the branch condition as predicate, otherwise
        // we must use the path predicate as there are ways to get from one
        // branch of the dominator to the other. We need to be careful if
        // either branches are directly to the join block. This is fine,
        // it's as if there was an empty block on that critical edge which
        // is dominated by that path.

        if (takenEdgep == ap || m_domTree.dominates(takenEdgep->dstp(), ap->srcp())) {
            if (untknEdgep == bp || m_domTree.dominates(untknEdgep->dstp(), bp->srcp())) {
                // Taken path dominates 'ap' and untaken dominates 'bp', use the branch condition
                ++m_ctx.m_synt.joinUsingBranchCondition;
                return std::make_tuple(m_bbToCondp[domp], ap->srcp(), bp->srcp());
            }
        } else if (takenEdgep == bp || m_domTree.dominates(takenEdgep->dstp(), bp->srcp())) {
            if (untknEdgep == ap || m_domTree.dominates(untknEdgep->dstp(), ap->srcp())) {
                // Taken path dominates 'bp' and untaken dominates 'ap', use the branch condition
                ++m_ctx.m_synt.joinUsingBranchCondition;
                return std::make_tuple(m_bbToCondp[domp], bp->srcp(), ap->srcp());
            }
        }

        // The branches don't dominate the joined blocks, must use the path predicate
        ++m_ctx.m_synt.joinUsingPathPredicate;

        // TODO: We could do better here: use the path predicate of the closest
        // cominating blocks, pick the one from the lower rank, etc, but this
        // generic case is very rare, most synthesizable logic has
        // series-parallel CFGs which are covered by the earlier cases.
        return std::make_tuple(m_edgeToPredicatep[ap], ap->srcp(), bp->srcp());
    }

    // Combine the output symbol tables of the predecessors of the given
    // block to compute the input symtol table for the given block.
    bool createInputSymbolTable(const CfgBlock& bb) {
        // The input symbol table of the given block, we are computing it now
        SymTab& joined = m_bbToISymTab[bb];

        // Input symbol table of entry block is special
        if (bb.isEnter()) {
            initializeEntrySymbolTable(joined);
            return true;
        }

        // Current input symbol table should be empty, we will fill it in here
        UASSERT(joined.empty(), "Unprocessed input symbol table should be empty");

        // Fast path if there is only one predecessor - TODO: use less copying
        if (!bb.isJoin()) {
            joined = m_bbToOSymTab[bb.firstPredecessorp()];
            return true;
        }

        // We also have a simpler job if there are 2 predecessors
        if (bb.isTwoWayJoin()) {
            DfgVertexVar* predicatep = nullptr;
            const CfgBlock* thenp = nullptr;
            const CfgBlock* elsep = nullptr;
            std::tie(predicatep, thenp, elsep)
                = howToJoin(bb.firstPredecessorEdgep(), bb.lastPredecessorEdgep());
            // Copy from else
            joined = m_bbToOSymTab[elsep];
            // Join with then
            return joinSymbolTables(joined, predicatep, m_bbToOSymTab[*thenp]);
        }

        // General hard way

        // Gather predecessors
        struct Predecessor final {
            const CfgBlock* m_bbp;  // Predeccessor block
            DfgVertexVar* m_predicatep;  // Predicate predecessor reached this block with
            const SymTab* m_oSymTabp;  // Output symbol table or predecessor
            Predecessor() = delete;
            Predecessor(const CfgBlock* bbp, DfgVertexVar* predicatep, const SymTab* oSymTabp)
                : m_bbp{bbp}
                , m_predicatep{predicatep}
                , m_oSymTabp{oSymTabp} {}
        };

        const std::vector<Predecessor> predecessors = [&]() {
            std::vector<Predecessor> res;
            for (const V3GraphEdge& edge : bb.inEdges()) {
                const CfgEdge& cfgEdge = static_cast<const CfgEdge&>(edge);
                const CfgBlock* const predecessorp = cfgEdge.srcp();
                DfgVertexVar* const predicatep = m_edgeToPredicatep[cfgEdge];
                const SymTab* const oSymTabp = &m_bbToOSymTab[predecessorp];
                res.emplace_back(predecessorp, predicatep, oSymTabp);
            }
            // Sort predecessors reverse topologically. This way earlier blocks
            // will come after later blocks, and the entry block is last if present.
            std::sort(res.begin(), res.end(), [](const Predecessor& a, const Predecessor& b) {  //
                return *a.m_bbp > *b.m_bbp;
            });
            return res;
        }();

        // Start by copying the bindings from the frist predecessor
        joined = *predecessors[0].m_oSymTabp;
        // Join over all other predecessors
        for (size_t i = 1; i < predecessors.size(); ++i) {
            DfgVertexVar* const predicatep = predecessors[i].m_predicatep;
            const SymTab& oSymTab = *predecessors[i].m_oSymTabp;
            if (!joinSymbolTables(joined, predicatep, oSymTab)) return false;
        }

        return true;
    }

    std::vector<Driver> computePropagatedDrivers(const std::vector<Driver>& newDrivers,
                                                 DfgVertexVar* oldp) {
        // Gather drivers of 'oldp' - they are in incresing range order with no overlaps
        std::vector<Driver> oldDrivers = gatherDrivers(oldp->srcp()->as<DfgVertexSplice>());
        UASSERT_OBJ(!oldDrivers.empty(), oldp, "Should have a proper driver");

        // Additional drivers of 'newp' propagated from 'oldp'
        std::vector<Driver> propagatedDrivers;

        // Add bits between 'msb' and 'lsb' from 'oldp' to 'pDrivers'
        const auto addOldDriver = [&](FileLine* const flp, uint32_t msb, uint32_t lsb) {
            UASSERT_OBJ(propagatedDrivers.empty() || lsb > propagatedDrivers.back().m_hi, flp,
                        "Drivers should be in ascending order");
            DfgSel* const selp = make<DfgSel>(flp, DfgDataType::packed(msb - lsb + 1));
            selp->lsb(lsb);
            selp->fromp(oldp);
            propagatedDrivers.emplace_back(selp, lsb, flp);
        };

        // Incorporate old drivers
        for (const Driver& oDriver : oldDrivers) {
            FileLine* const flp = oDriver.m_flp;
            // Range to consider inserting, we will adjust oldLo as we process drivers
            uint32_t oldLo = oDriver.m_lo;
            const uint32_t oldHi = oDriver.m_hi;

            // Loop for now, can move to bisection search if this is a problem, shouldn't be ...
            for (const Driver& nDriver : newDrivers) {
                UASSERT_OBJ(oldHi >= oldLo, flp, "Should have stopped iteration");
                // If new driver is entirely below old driver, move on to
                if (nDriver.m_hi < oldLo) continue;
                // If new driver is entirely above old driver, we can stop
                if (oldHi < nDriver.m_lo) break;

                // There is an overlap between 'oDriver' and 'nDriver'.
                // Insert the low bits and adjust the insertion range.
                // The rest will take care of itself on subsequent iterations.
                if (oldLo < nDriver.m_lo) addOldDriver(flp, nDriver.m_lo - 1, oldLo);
                oldLo = nDriver.m_hi + 1;

                // Stop if no more bits remaining in the old driver
                if (oldLo > oldHi) break;
            }

            // Insert remaining bits if any
            if (oldHi >= oldLo) addOldDriver(flp, oldHi, oldLo);
        }

        return propagatedDrivers;
    }

    // Given the drivers of a variable after converting a single statement
    // 'newp', add drivers from 'oldp' that were not reassigned be drivers
    // in newp. This computes the total result of all previous assignments.
    bool incorporatePreviousValue(Variable* varp, DfgVertexVar* newp, DfgVertexVar* oldp) {
        UASSERT_OBJ(newp->srcp(), varp, "Assigned variable has no driver");

        // Easy if there is no old value...
        if (!oldp) return true;

        // New driver was not yet coalesced, so should always be a splice
        DfgVertexSplice* const nSplicep = newp->srcp()->as<DfgVertexSplice>();

        // If the old value is the real variable we just computed the new value for,
        // then it is the circular feedback into the synthesized block, add it as default driver.
        if (oldp->nodep() == varp) {
            if (!nSplicep->wholep()) newp->defaultp(oldp);
            return true;
        }

        UASSERT_OBJ(oldp->srcp(), varp, "Previously assigned variable has no driver");

        // Can't do arrays yet
        if (!newp->isPacked()) {
            ++m_ctx.m_synt.nonSynArray;
            return false;
        }

        // Gather drivers of 'newp' - they are in incresing range order with no overlaps
        UASSERT_OBJ(!newp->defaultp(), newp, "Converted value should not have default");
        std::vector<Driver> nDrivers = gatherDrivers(newp->srcp()->as<DfgVertexSplice>());
        UASSERT_OBJ(!nDrivers.empty(), newp, "Should have a proper driver");

        // Additional drivers of 'newp' propagated from 'oldp'
        std::vector<Driver> pDrivers = computePropagatedDrivers(nDrivers, oldp);

        if (!pDrivers.empty()) {
            // Need to merge propagated sources, so reset the splice
            nSplicep->resetDrivers();
            // Merge drivers - they are both sorted and non-overlapping
            std::vector<Driver> drivers;
            drivers.reserve(nDrivers.size() + pDrivers.size());
            std::merge(nDrivers.begin(), nDrivers.end(), pDrivers.begin(), pDrivers.end(),
                       std::back_inserter(drivers));
            // Coalesce adjacent ranges
            coalesceDrivers(drivers);
            // Reinsert drivers in order
            for (const Driver& d : drivers) nSplicep->addDriver(d.m_vtxp, d.m_lo, d.m_flp);
        }

        // If the old had a default, add to the new one too, unless redundant
        if (oldp->defaultp() && !nSplicep->wholep()) newp->defaultp(oldp->defaultp());

        // Done
        return true;
    }

    // Synthesize the given statements with the given input symbol table.
    // Returns true if successfolly synthesized.
    // Populates the given output symbol table.
    // Populates the given reference with the condition of the terminator branch, if any.
    bool synthesizeBasicBlock(SymTab& oSymTab, DfgVertex*& condpr,
                              const std::vector<AstNodeStmt*>& stmtps, const SymTab& iSymTab) {
        // Use fresh set of vertices in m_converter
        const VNUser2InUse user2InUse;

        // Initialize Variable -> Vertex bindings available in this block
        for (const auto& pair : iSymTab) {
            Variable* const varp = pair.first;
            DfgVertexVar* const vtxp = pair.second;
            varp->user2p(vtxp);
            oSymTab[varp] = vtxp;
        }

        // Synthesize each statement one after the other
        std::vector<std::pair<Variable*, DfgVertexVar*>> updates;
        for (AstNodeStmt* const stmtp : stmtps) {
            // Regular statements
            if (AstAssign* const ap = VN_CAST(stmtp, Assign)) {
                // Convert this assignment
                if (!m_converter.convert(updates, *m_logicp, ap)) {
                    ++m_ctx.m_synt.nonSynConv;
                    return false;
                }
                // Apply variable updates from this statement
                for (const auto& pair : updates) {
                    // The target variable that was assigned to
                    Variable* const varp = pair.first;
                    // The new, potentially partially assigned value
                    DfgVertexVar* const newp = pair.second;
                    // Normalize drivers within this statement, bail if multidriven
                    DfgVertexSplice* const srcp = newp->srcp()->as<DfgVertexSplice>();
                    std::vector<Driver> drivers = gatherDrivers(srcp);
                    const bool single = drivers.size() == 1;
                    if (!normalizeDrivers(*newp, drivers)) {
                        getAstVar(varp)->setDfgMultidriven();
                        ++m_ctx.m_synt.nonSynMultidrive;
                        return false;
                    }
                    // If there were more than one driver (often not), re-add in case coalesced
                    if (!single) {
                        srcp->resetDrivers();
                        for (const Driver& d : drivers) srcp->addDriver(d.m_vtxp, d.m_lo, d.m_flp);
                    }
                    // The old value, if any
                    DfgVertexVar* const oldp = varp->user2u().template to<DfgVertexVar*>();
                    // Inncorporate old value into the new value
                    if (!incorporatePreviousValue(varp, newp, oldp)) return false;
                    // Update binding of target variable
                    varp->user2p(newp);
                    // Update output symbol table of this block
                    oSymTab[varp] = newp;
                }
                updates.clear();
                continue;
            }

            // Terminator branches
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                UASSERT_OBJ(ifp == stmtps.back(), ifp, "Branch should be last statement");
                // Convert condition, give up if failed
                DfgVertex* condp = m_converter.convert(*m_logicp, ifp->condp());
                if (!condp) {
                    ++m_ctx.m_synt.nonSynConv;
                    return false;
                }
                // Single bit condition can be use directly, otherwise: use 'condp != 0'
                if (condp->width() != 1) {
                    FileLine* const flp = condp->fileline();
                    DfgNeq* const neqp = make<DfgNeq>(flp, DfgDataType::packed(1));
                    neqp->lhsp(make<DfgConst>(flp, condp->width(), 0U));
                    neqp->rhsp(condp);
                    condp = neqp;
                }
                condpr = condp;
                continue;
            }

            // Unhandled
            ++m_ctx.m_synt.nonSynStmt;
            return false;
        }

        return true;
    }

    // Assign path predicates to the outgoing control flow edges of the given block
    void assignPathPredicates(const CfgBlock& bb) {
        // Nothing to do for the exit block
        if (bb.isExit()) return;

        // Get the predicate of this block
        DfgVertex* const predp = [&]() -> DfgVertex* {
            // Entry block has no predecessors, use constant true
            if (bb.isEnter()) return make<DfgConst>(m_logicp->fileline(), 1U, 1U);

            // For any other block, 'or' together all the incoming predicates
            const auto& inEdges = bb.inEdges();
            auto it = inEdges.begin();
            DfgVertex* resp = m_edgeToPredicatep[static_cast<const CfgEdge&>(*it)];
            while (++it != inEdges.end()) {
                DfgOr* const orp = make<DfgOr>(resp->fileline(), resp->dtype());
                orp->rhsp(resp);
                orp->lhsp(m_edgeToPredicatep[static_cast<const CfgEdge&>(*it)]);
                resp = orp;
            }
            return resp;
        }();

        size_t n = m_nPathPred++;  // Sequence number for temporaries
        const DfgDataType& dtype = predp->dtype();

        const auto mkTmp = [&](FileLine* flp, const char* name, DfgVertex* srcp) {
            const std::string prefix = "_BB" + std::to_string(bb.id()) + "_" + name;
            DfgVertexVar* const tmpp = m_converter.createTmp(*m_logicp, flp, dtype, prefix, n);
            tmpp->srcp(srcp);
            return tmpp;
        };

        // Assign it to a variable in case it's used multiple times
        DfgVertexVar* const pInp = mkTmp(predp->fileline(), "PathIn", predp);

        // For uncondional branches, the successor predicate edge is the same
        if (!bb.isBranch()) {
            m_edgeToPredicatep[bb.takenEdgep()] = mkTmp(pInp->fileline(), "Goto", pInp);
            return;
        }

        // For branches, we need to factor in the branch condition
        DfgVertex* const condp = m_bbToCondp[bb];
        FileLine* const flp = condp->fileline();

        // Predicate for taken branch: 'predp & condp'
        {
            DfgAnd* const takenPredp = make<DfgAnd>(flp, dtype);
            takenPredp->lhsp(pInp);
            takenPredp->rhsp(condp);
            m_edgeToPredicatep[bb.takenEdgep()] = mkTmp(flp, "Taken", takenPredp);
        }

        // Predicate for untaken branch: 'predp & ~condp'
        {
            DfgAnd* const untknPredp = make<DfgAnd>(flp, dtype);
            untknPredp->lhsp(pInp);
            DfgNot* const notp = make<DfgNot>(flp, dtype);
            notp->srcp(condp);
            untknPredp->rhsp(notp);
            m_edgeToPredicatep[bb.untknEdgep()] = mkTmp(flp, "Untkn", untknPredp);
        }
    }

    // Returns true if all external updates to volatile variables are observed correctly
    bool checkExtWrites() {
        for (const DfgVertex* const vtxp : m_logicp->synth()) {
            const DfgVertexVar* const varp = vtxp->cast<DfgVertexVar>();
            if (!varp) continue;
            // If the variable we synthesized this vertex for is volatile, and
            // the value of the synthesized temporary is observed, we might be
            // missing an external update, so we mut give up.
            if (!varp->hasSinks()) continue;
            if (!DfgVertexVar::isVolatile(varp->tmpForp())) continue;
            ++m_ctx.m_synt.nonSynExtWrite;
            return false;
        }
        return true;
    }

    // Add the synthesized values as drivers to the output variables of the current DfgLogic
    bool addSynthesizedOutput(SymTab& oSymTab) {
        // It's possible we think a variable is written by the DfgLogic when
        // it actauly isn't, e.g.: '{a[0], b[0]}[1] = ...' does not write 'b'.
        // These LHS forms can happen after some earlier tranforms. We
        // should just run V3Const on them earlier, but we will do belt and
        // braces and check here too. We can't touch any output variables if so.
        const bool missing = m_logicp->foreachSink([&](const DfgVertex& sink) {
            const DfgUnresolved* const unresolvedp = sink.as<DfgUnresolved>();
            AstNode* const tgtp = unresolvedp->singleSink()->as<DfgVertexVar>()->nodep();
            // cppcheck-suppress constVariablePointer
            Variable* const varp = reinterpret_cast<Variable*>(tgtp);
            return !oSymTab.count(varp);
        });
        if (missing) {
            ++m_ctx.m_synt.nonSynFalseWrite;
            return false;
        }

        // Add sinks to read the computed values for the target variables
        return !m_logicp->foreachSink([&](DfgVertex& sink) {
            DfgUnresolved* const unresolvedp = sink.as<DfgUnresolved>();
            const DfgVertexVar* const varp = unresolvedp->singleSink()->as<DfgVertexVar>();
            DfgVertexVar* const resp = oSymTab.at(reinterpret_cast<Variable*>(varp->nodep()));
            UASSERT_OBJ(resp->srcp(), resp, "Undriven result");

            // If the output is not used further in the synthesized logic itself,
            // then resp will be deleted before we return, so we can just use
            // its splice directly without ending up with a multi-use operation.
            if (!resp->hasSinks()) {
                unresolvedp->addDriver(resp->srcp()->as<DfgVertexSplice>());
                return false;  // OK, continue.
            }

            // TODO: computePropagatedDrivers cannot handle arrays, should
            // never happen with simple continous assignments
            if (!resp->isPacked()) {
                ++m_ctx.m_synt.nonSynArray;
                return true;  // Not OK, give up
            }

            // We need to add a new splice to avoid multi-use of the original splice
            DfgSplicePacked* const splicep
                = new DfgSplicePacked{m_dfg, resp->fileline(), resp->dtype()};
            // Drivers are the same
            const std::vector<Driver> drivers = computePropagatedDrivers({}, resp);
            for (const Driver& d : drivers) splicep->addDriver(d.m_vtxp, d.m_lo, d.m_flp);
            unresolvedp->addDriver(splicep);
            return false;  // OK, continue
        });
    }

    // Synthesize the given AstAssignW. Returns true on success.
    bool synthesizeAssignW(AstAssignW* nodep) {
        ++m_ctx.m_synt.inputAssign;

        // Construct an equivalent AstAssign
        AstNodeExpr* const lhsp = nodep->lhsp()->cloneTree(false);
        AstNodeExpr* const rhsp = nodep->rhsp()->cloneTree(false);
        AstAssign* const assignp = new AstAssign{nodep->fileline(), lhsp, rhsp};

        // The input and output symbol tables
        SymTab iSymTab;
        SymTab oSymTab;

        // Initialzie input symbol table
        initializeEntrySymbolTable(iSymTab);

        // Synthesize as if it was in a single CfgBlock CFG
        DfgVertex* condp = nullptr;
        const bool success = synthesizeBasicBlock(oSymTab, condp, {assignp}, iSymTab);
        UASSERT_OBJ(!condp, nodep, "Conditional AstAssignW ???");
        // Delete auxiliary AstAssign
        VL_DO_DANGLING(assignp->deleteTree(), assignp);
        if (!success) return false;

        // Check exernal writes are observed correctly
        if (!checkExtWrites()) return false;

        // Add resolved output variable drivers
        return addSynthesizedOutput(oSymTab);
    }

    // Synthesize the given AstAlways. Returns true on success.
    bool synthesizeCfg(CfgGraph& cfg) {
        ++m_ctx.m_synt.inputAlways;

        // If there is a backward edge (loop), we can't synthesize it
        if (cfg.containsLoop()) {
            ++m_ctx.m_synt.nonSynLoop;
            ++m_ctx.m_synt.cfgCyclic;
            return false;
        }

        // If it's a trivial CFG we can save on some work
        if (cfg.nBlocks() == 1) {
            ++m_ctx.m_synt.cfgTrivial;
        } else {
            // Insert two-way join blocks to aid multiplexer ordering
            if (cfg.insertTwoWayJoins()) {
                ++m_ctx.m_synt.cfgSp;
            } else {
                ++m_ctx.m_synt.cfgDag;
            }
            // Initialize maps needed for non-trivial CFGs
            m_domTree = CfgDominatorTree{cfg};
            m_edgeToPredicatep = cfg.makeEdgeMap<DfgVertexVar*>();
        }

        // Initialize CfgMaps
        m_bbToISymTab = cfg.makeBlockMap<SymTab>();
        m_bbToOSymTab = cfg.makeBlockMap<SymTab>();
        m_bbToCondp = cfg.makeBlockMap<DfgVertexVar*>();

        // Synthesize all blocks
        for (const V3GraphVertex& vtx : cfg.vertices()) {
            const CfgBlock& bb = static_cast<const CfgBlock&>(vtx);
            // Prepare the input symbol table of this block (enter, or join predecessor blocks)
            if (!createInputSymbolTable(bb)) return false;
            // Synthesize this block
            DfgVertex* condp = nullptr;
            if (!synthesizeBasicBlock(m_bbToOSymTab[bb], condp, bb.stmtps(), m_bbToISymTab[bb])) {
                return false;
            }
            // Create a temporary for the branch condition as it might be used multiple times
            if (condp) {
                FileLine* const flp = condp->fileline();
                const DfgDataType& dtype = condp->dtype();
                const std::string prefix = "_BB" + std::to_string(bb.id()) + "_Cond";
                const size_t n = m_nBranchCond++;
                DfgVertexVar* const vp = m_converter.createTmp(*m_logicp, flp, dtype, prefix, n);
                vp->srcp(condp);
                m_bbToCondp[bb] = vp;
            }
            // Set the path predicates on the successor edges
            assignPathPredicates(bb);
        }

        // Check exernal writes are observed correctly
        if (!checkExtWrites()) return false;

        // Add resolved output variable drivers
        return addSynthesizedOutput(m_bbToOSymTab[cfg.exit()]);
    }

    // Synthesize a DfgLogic into regular vertices. Returns ture on success.
    bool synthesize(DfgLogic& vtx) {
        VL_RESTORER(m_logicp);
        m_logicp = &vtx;

        if (AstAssignW* const ap = VN_CAST(vtx.nodep()->stmtsp(), AssignW)) {
            if (ap->nextp()) return false;
            if (!synthesizeAssignW(ap)) return false;
            ++m_ctx.m_synt.synthAssign;
            return true;
        }

        if (!synthesizeCfg(vtx.cfg())) return false;
        ++m_ctx.m_synt.synthAlways;
        return true;
    }

    // Revert all DfgLogic in m_toRevert, or DfgLogic driving the DfgUnresolved
    // vertices in m_toRevert, and transitively the same for any DfgUnresolved
    // driven by the reverted DfgLogic. Delete all DfgUnresolved involed.
    void revert(VDouble0& statCountr) {
        m_toRevert.foreach([&](DfgVertex& vtx) {
            // Process DfgLogic
            if (DfgLogic* const vtxp = vtx.cast<DfgLogic>()) {
                UASSERT_OBJ(vtxp->selectedForSynthesis(), vtxp, "Shouldn't reach here unselected");
                // Revert this logic
                UASSERT_OBJ(!vtxp->reverted(), vtxp, "Should be reverting now");
                ++statCountr;
                for (DfgVertex* const p : vtxp->synth()) VL_DO_DANGLING(p->unlinkDelete(m_dfg), p);
                vtxp->synth().clear();
                vtxp->setReverted();
                // Add all DfgUnresolved it drives to the work list
                vtxp->foreachSink([&](DfgVertex& snk) {
                    m_toRevert.push_front(*snk.as<DfgUnresolved>());
                    return false;
                });
                return;
            }

            // Process DfgUnresolved
            if (DfgUnresolved* const vtxp = vtx.cast<DfgUnresolved>()) {
                // The result variable will be driven from Ast code, mark as such
                vtxp->singleSink()->as<DfgVertexVar>()->setHasModWrRefs();
                // Add all driving DfgLogic to the work list
                vtxp->foreachSource([&](DfgVertex& src) {
                    DfgLogic* const lp = src.cast<DfgLogic>();
                    if (lp && !lp->reverted()) m_toRevert.push_front(*lp);
                    return false;
                });
                // Delete the DfgUnresolved driver
                VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
                return;
            }

            // There should be nothing else on the worklist
            vtx.v3fatalSrc("Unexpected vertex type");
        });
    }

    // Synthesize all of the given vertices
    void main() {
        //-------------------------------------------------------------------
        UINFO(5, "Step 0: Remove all DfgLogic not selected for synthesis");
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            // Only processing DfgUnresolved
            if (!vtxp->is<DfgUnresolved>()) continue;
            bool anySelected = false;
            bool anyUnselected = false;
            vtxp->foreachSource([&](DfgVertex& src) {
                const DfgLogic& logic = *src.as<DfgLogic>();
                if (logic.selectedForSynthesis()) {
                    anySelected = true;
                } else {
                    anyUnselected = true;
                }
                return false;
            });
            // There should be a driver
            UASSERT_OBJ(anySelected || anyUnselected, vtxp, "'DfgUnresolved' with no driver");
            // All drivers should be selected or all should be unselected
            UASSERT_OBJ(!(anySelected && anyUnselected), vtxp, "Invalid 'DfgLogic' selection");
            // If all drivers are unselected, delete this DfgUnresolved here
            if (anyUnselected) {
                // The result variable will be driven from Ast code, mark as such
                vtxp->singleSink()->as<DfgVertexVar>()->setHasModWrRefs();
                VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
            }
        }
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            // Only processing DfgLogic
            DfgLogic* const logicp = vtxp->cast<DfgLogic>();
            if (!logicp) continue;
            if (logicp->selectedForSynthesis()) continue;
            // There should be no sinks left for unselected DfgLogic, delete them here
            UASSERT_OBJ(!logicp->hasSinks(), vtxp, "Unselected 'DfgLogic' with sinks remaining");
            // Input variables will be read in Ast code, mark as such
            logicp->foreachSource([](DfgVertex& src) {
                src.as<DfgVertexVar>()->setHasModRdRefs();
                return false;
            });
            VL_DO_DANGLING(logicp->unlinkDelete(m_dfg), logicp);
        }
        debugDump("synth-selected");

        //-------------------------------------------------------------------
        UINFO(5, "Step 1: Attempting to synthesize each of the selected DfgLogic");
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            DfgLogic* const logicp = vtx.cast<DfgLogic>();
            if (!logicp) continue;

            // We should only have DfgLogic remaining that was selected for synthesis
            UASSERT_OBJ(logicp->selectedForSynthesis(), logicp, "Unselected DfgLogic remains");

            // Debug aid
            if (VL_UNLIKELY(s_dfgSynthDebugLimit)) {
                if (s_dfgSynthDebugCount == s_dfgSynthDebugLimit) break;
                ++s_dfgSynthDebugCount;
                if (s_dfgSynthDebugCount == s_dfgSynthDebugLimit) {
                    // This is the breaking logic
                    m_debugLogicp = logicp;
                    // Dump it
                    UINFOTREE(0, logicp->nodep(), "Problematic DfgLogic: " << logicp, "  ");
                    V3EmitV::debugVerilogForTree(logicp->nodep(), std::cout);
                    debugDump("synth-lastok");
                }
            }

            // Synthesize it, if failed, enqueue for reversion
            if (!synthesize(*logicp)) {
                logicp->setNonSynthesizable();
                m_toRevert.push_front(*logicp);
            }
        }
        debugDump("synth-converted");

        //-------------------------------------------------------------------
        UINFO(5, "Step 2: Revert drivers of variables with unsynthesizeable drivers");
        // We do this as the variables might be multi-driven, we can't know if synthesis failed
        revert(m_ctx.m_synt.revertNonSyn);
        debugDump("synth-reverted");

        //-------------------------------------------------------------------
        UINFO(5, "Step 3: Resolve synthesized drivers of original (non-temporary) variables");
        // List of multi-driven variables
        std::vector<DfgVertexVar*> multidrivenps;
        // Map from variable to its resolved driver
        std::unordered_map<const DfgVertexVar*, DfgVertexSplice*> resolvedDrivers;
        // Compute resolved drivers of all variablees
        for (DfgVertexVar& var : m_dfg.varVertices()) {
            if (!var.srcp()) continue;
            DfgUnresolved* const unresolvedp = var.srcp()->cast<DfgUnresolved>();
            if (!unresolvedp) break;  // Stop when reached the synthesized temporaries

            // Resolve the synthesized drivers
            DfgVertexSplice* const resolvedp = [&]() -> DfgVertexSplice* {
                // All synthesized drivers were normalized already,
                // so if there is only one, it can be used directly
                if (unresolvedp->nInputs() == 1) {
                    return unresolvedp->inputp(0)->as<DfgVertexSplice>();
                }
                // Otherwise gather the synthesized drivers
                std::vector<Driver> drivers = gatherDriversUnresolved(unresolvedp);
                // Normalize them, make resolved driver if all good
                if (normalizeDrivers(var, drivers)) return makeSplice(var, drivers);
                // If mutlidriven, record and ignore
                multidrivenps.emplace_back(&var);
                m_toRevert.push_front(*unresolvedp);
                return nullptr;
            }();
            // Bail if multidriven
            if (!resolvedp) continue;
            // Add to map for next loop
            const bool newEntry = resolvedDrivers.emplace(&var, resolvedp).second;
            UASSERT_OBJ(newEntry, &var, "Dupliacte driver");
        }
        // Mark as multidriven for future DFG runs - here, so we get all warnings above
        for (const DfgVertexVar* const vtxp : multidrivenps) vtxp->varp()->setDfgMultidriven();
        // Revert and remove drivers of multi-driven variables
        revert(m_ctx.m_synt.revertMultidrive);
        // Replace all DfgUnresolved with the resolved drivers
        for (const DfgVertexVar& var : m_dfg.varVertices()) {
            if (!var.srcp()) continue;
            DfgUnresolved* const srcp = var.srcp()->cast<DfgUnresolved>();
            if (!srcp) break;  // Stop when reached the synthesized temporaries

            // Replace it
            srcp->replaceWith(resolvedDrivers.at(&var));
            VL_DO_DANGLING(srcp->unlinkDelete(m_dfg), srcp);
        }
        debugDump("synth-resolved");

        //-------------------------------------------------------------------
        UINFO(5, "Step 4: Remove all remaining DfgLogic and DfgUnresolved");
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            // Previous step should have removed all DfgUnresolved
            UASSERT_OBJ(!vtxp->is<DfgUnresolved>(), vtxp, "DfgUnresolved remains");

            // Process only DfgLogic
            DfgLogic* const logicp = vtxp->cast<DfgLogic>();
            if (!logicp) continue;

            // Earlier pass should have removed all sinks
            UASSERT_OBJ(!logicp->hasSinks(), logicp, "DfgLogic sink remains");

            if (!logicp->synth().empty()) {
                // If synthesized, delete the corresponding AstNode. It is now in Dfg.
                logicp->nodep()->unlinkFrBack()->deleteTree();
            } else {
                // Not synthesized. Logic stays in Ast. Mark source  variables
                //as read in module. Outputs already marked by revertTransivelyAndRemove.
                logicp->foreachSource([](DfgVertex& src) {  //
                    src.as<DfgVertexVar>()->setHasModRdRefs();
                    return false;
                });
            }

            // Delete this DfgLogic
            VL_DO_DANGLING(logicp->unlinkDelete(m_dfg), logicp);
        }
        // Reset the debug pointer, we have deleted it in the loop above ...
        m_debugLogicp = nullptr;
        debugDump("synth-rmlogics");

        //-------------------------------------------------------------------
        UINFO(5, "Step 5: Remove unnecessary splices");
        for (DfgVertex* const vtxp : m_dfg.opVertices().unlinkable()) {
            DfgVertexSplice* const splicep = vtxp->cast<DfgVertexSplice>();
            if (!splicep) continue;

            // Might not have a sink if the driving logic was revered, remove
            if (!splicep->hasSinks()) {
                VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
                continue;
            }

            // It should alway have drivers
            UASSERT_OBJ(splicep->nInputs(), splicep, "Splice with no drivers");

            // If redundant, remove it
            if (DfgVertex* const wholep = splicep->wholep()) {
                if (DfgVertexVar* const varp = splicep->singleSink()->cast<DfgVertexVar>()) {
                    varp->driverFileLine(splicep->driverFileLine(0));
                }
                splicep->replaceWith(wholep);
                VL_DO_DANGLING(splicep->unlinkDelete(m_dfg), splicep);
            }
        }
        debugDump("synth-rmsplice");
    }

    // CONSTRUCTOR
    AstToDfgSynthesize(DfgGraph& dfg, V3DfgSynthesisContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx}
        , m_converter{dfg, ctx} {
        main();
    }

public:
    static void apply(DfgGraph& dfg, V3DfgSynthesisContext& ctx) {
        AstToDfgSynthesize{dfg, ctx};

        // Final step outside, as both AstToDfgSynthesize and removeUnused used DfgUserMap
        UINFO(5, "Step 6: Remove all unused vertices");
        V3DfgPasses::removeUnused(dfg);
        if (dumpDfgLevel() >= 9) dfg.dumpDotFilePrefixed(ctx.prefix() + "synth-rmunused");

        // No operation vertex should have multiple sinks. Cyclic decomoposition
        // depends on this and it can easily be ensured by using temporaries.
        // Also, all sources should be connected at this point
        if (v3Global.opt.debugCheck()) {
            for (DfgVertex& vtx : dfg.opVertices()) {
                UASSERT_OBJ(!vtx.hasMultipleSinks(), &vtx, "Operation has multiple sinks");
                for (size_t i = 0; i < vtx.nInputs(); ++i) {
                    UASSERT_OBJ(vtx.inputp(i), &vtx, "Unconnected source operand");
                }
            }
            V3DfgPasses::typeCheck(dfg);
        }
    }
};

// Decide which DfgLogic to attempt to synthesize
static void dfgSelectLogicForSynthesis(DfgGraph& dfg) {
    // If we are told to synthesize everything, we will do so ...
    if (v3Global.opt.fDfgSynthesizeAll()) {
        for (DfgVertex& vtx : dfg.opVertices()) {
            if (DfgLogic* const logicp = vtx.cast<DfgLogic>()) logicp->setSelectedForSynthesis();
        }
        return;
    }

    // Otherwise figure out which vertices are likely worth synthesizing.

    // Bather circular variables
    std::vector<DfgVertexVar*> circularVarps;
    {
        DfgUserMap<uint64_t> scc = dfg.makeUserMap<uint64_t>();
        V3DfgPasses::colorStronglyConnectedComponents(dfg, scc);
        for (DfgVertexVar& var : dfg.varVertices()) {
            if (!scc.at(var)) continue;
            // This is a circular variable
            circularVarps.emplace_back(&var);
        }
    }

    // We need to expand the selection to cover all drivers, use a work list
    DfgWorklist worklist{dfg};

    // Synthesize all drivers of circular variables
    for (const DfgVertexVar* const varp : circularVarps) {
        varp->srcp()->as<DfgUnresolved>()->foreachSource([&](DfgVertex& driver) {
            worklist.push_front(*driver.as<DfgLogic>());
            return false;
        });
    }

    // Synthesize all continuous assignments and simple blocks driving exactly
    // one variable. This is approximately the old default behaviour of Dfg.
    for (DfgVertex& vtx : dfg.opVertices()) {
        DfgLogic* const logicp = vtx.cast<DfgLogic>();
        if (!logicp) continue;
        if (logicp->nodep()->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            worklist.push_front(*logicp);
            continue;
        }
        const CfgGraph& cfg = logicp->cfg();
        if (!logicp->hasMultipleSinks() && cfg.nBlocks() <= 4 && cfg.nEdges() <= 4) {
            worklist.push_front(*logicp);
        }
    }

    // Now expand to cover all logic driving the same set of variables and mark
    worklist.foreach([&](DfgVertex& vtx) {
        DfgLogic& logic = *vtx.as<DfgLogic>();
        UASSERT_OBJ(!logic.selectedForSynthesis(), &vtx, "Should not be visited twice");
        // Mark as selected for synthesis
        logic.setSelectedForSynthesis();
        // Enqueue all other logic driving the same variables as this one
        logic.foreachSink([&](DfgVertex& sink) {
            sink.as<DfgUnresolved>()->foreachSource([&](DfgVertex& sibling) {
                DfgLogic& siblingLogic = *sibling.as<DfgLogic>();
                if (!siblingLogic.selectedForSynthesis()) worklist.push_front(siblingLogic);
                return false;
            });
            return false;
        });
    });
}

void V3DfgPasses::synthesize(DfgGraph& dfg, V3DfgContext& ctx) {
    // Select which DfgLogic to attempt to synthesize
    dfgSelectLogicForSynthesis(dfg);
    // Synthesize them - also removes un-synthesized DfgLogic, so must run even if nothing selected
    if (dfg.modulep()) {
        AstToDfgSynthesize</* T_Scoped: */ false>::apply(dfg, ctx.m_synthContext);
    } else {
        AstToDfgSynthesize</* T_Scoped: */ true>::apply(dfg, ctx.m_synthContext);
    }
}
