// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Peephole optimizations over DfgGraph
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
//
// A pattern-matching based optimizer for DfgGraph. This is in some aspects
// similar to V3Const, but more powerful in that it does not care about
// ordering combinational statement. This is also less broadly applicable
// than V3Const, as it does not apply to procedural statements with
// sequential execution semantics.
//
// Each pattern can look at a certain number of source vertices to see
// if a simplified form can be introduced. Some patterns also look at the
// immediate sinks of some vertices. Ideally the algorithm should run to
// fixed point (until nothing else changes). To do this efficiently, two
// lists of vertices are maintained:
// - the 'work' list contains vertices to be considered on the current
//   iteration
// - the 'iter' list contains vertices whose whole neighborhood could be
//   considered on the next iteration
// The 'work' list ensures simple cascading pattern applications are
// handled in a single pass. The 'iter' list ensures the algorithm runs
// to fixed point if no pattern looks deeper across the graph than the
// neighborhood considered on the next iteration.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgCache.h"
#include "V3DfgPasses.h"
#include "V3DfgPeepholePatterns.h"
#include "V3Stats.h"

#include <algorithm>
#include <cctype>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

V3DfgPeepholeContext::V3DfgPeepholeContext(V3DfgContext& ctx, const std::string& label)
    : V3DfgSubContext{ctx, label, "Peephole"} {
    const auto checkEnabled = [this](VDfgPeepholePattern id) {
        std::string str{id.ascii()};
        std::transform(str.begin(), str.end(), str.begin(), [](unsigned char c) {  //
            return c == '_' ? '-' : std::tolower(c);
        });
        m_enabled[id] = v3Global.opt.fDfgPeepholeEnabled(str);
    };
#define OPTIMIZATION_CHECK_ENABLED(id, name) checkEnabled(VDfgPeepholePattern::id);
    FOR_EACH_DFG_PEEPHOLE_OPTIMIZATION(OPTIMIZATION_CHECK_ENABLED)
#undef OPTIMIZATION_CHECK_ENABLED
}

V3DfgPeepholeContext::~V3DfgPeepholeContext() {
    for (AstNode* const nodep : m_deleteps) {
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    const auto emitStat = [this](VDfgPeepholePattern id) {
        std::string str{id.ascii()};
        std::transform(str.begin(), str.end(), str.begin(), [](unsigned char c) {  //
            return c == '_' ? ' ' : std::tolower(c);
        });
        addStat(str, m_count[id]);
    };
#define OPTIMIZATION_EMIT_STATS(id, name) emitStat(VDfgPeepholePattern::id);
    FOR_EACH_DFG_PEEPHOLE_OPTIMIZATION(OPTIMIZATION_EMIT_STATS)
#undef OPTIMIZATION_EMIT_STATS
}

// clang-format off
template <typename T_Reduction>
struct ReductionToBitwiseImpl {};
template <> struct ReductionToBitwiseImpl<DfgRedAnd> { using type = DfgAnd; };
template <> struct ReductionToBitwiseImpl<DfgRedOr>  { using type = DfgOr;  };
template <> struct ReductionToBitwiseImpl<DfgRedXor> { using type = DfgXor; };
template <typename T_Reduction>
using ReductionToBitwise = typename ReductionToBitwiseImpl<T_Reduction>::type;

template <typename T_Bitwise>
struct BitwiseToReductionImpl {};
template <> struct BitwiseToReductionImpl<DfgAnd> { using type = DfgRedAnd; };
template <> struct BitwiseToReductionImpl<DfgOr>  { using type = DfgRedOr;  };
template <> struct BitwiseToReductionImpl<DfgXor> { using type = DfgRedXor; };
template <typename T_Reduction>
using BitwiseToReduction = typename BitwiseToReductionImpl<T_Reduction>::type;

namespace {
template<typename Vertex> void foldOp(V3Number& out, const V3Number& src);
template <> void foldOp<DfgExtend>     (V3Number& out, const V3Number& src) { out.opAssign(src); }
template <> void foldOp<DfgExtendS>    (V3Number& out, const V3Number& src) { out.opExtendS(src, src.width()); }
template <> void foldOp<DfgLogNot>     (V3Number& out, const V3Number& src) { out.opLogNot(src); }
template <> void foldOp<DfgNegate>     (V3Number& out, const V3Number& src) { out.opNegate(src); }
template <> void foldOp<DfgNot>        (V3Number& out, const V3Number& src) { out.opNot(src); }
template <> void foldOp<DfgRedAnd>     (V3Number& out, const V3Number& src) { out.opRedAnd(src); }
template <> void foldOp<DfgRedOr>      (V3Number& out, const V3Number& src) { out.opRedOr(src); }
template <> void foldOp<DfgRedXor>     (V3Number& out, const V3Number& src) { out.opRedXor(src); }

template<typename Vertex> void foldOp(V3Number& out, const V3Number& lhs, const V3Number& rhs);
template <> void foldOp<DfgAdd>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAdd(lhs, rhs); }
template <> void foldOp<DfgAnd>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAnd(lhs, rhs); }
template <> void foldOp<DfgConcat>     (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opConcat(lhs, rhs); }
template <> void foldOp<DfgDiv>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDiv(lhs, rhs); }
template <> void foldOp<DfgDivS>       (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDivS(lhs, rhs); }
template <> void foldOp<DfgEq>         (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opEq(lhs, rhs); }
template <> void foldOp<DfgGt>         (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGt(lhs, rhs); }
template <> void foldOp<DfgGtS>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGtS(lhs, rhs); }
template <> void foldOp<DfgGte>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGte(lhs, rhs); }
template <> void foldOp<DfgGteS>       (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGteS(lhs, rhs); }
template <> void foldOp<DfgLogAnd>     (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogAnd(lhs, rhs); }
template <> void foldOp<DfgLogEq>      (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogEq(lhs, rhs); }
template <> void foldOp<DfgLogIf>      (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogIf(lhs, rhs); }
template <> void foldOp<DfgLogOr>      (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogOr(lhs, rhs); }
template <> void foldOp<DfgLt>         (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLt(lhs, rhs); }
template <> void foldOp<DfgLtS>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLtS(lhs, rhs); }
template <> void foldOp<DfgLte>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLte(lhs, rhs); }
template <> void foldOp<DfgLteS>       (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLteS(lhs, rhs); }
template <> void foldOp<DfgModDiv>     (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDiv(lhs, rhs); }
template <> void foldOp<DfgModDivS>    (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDivS(lhs, rhs); }
template <> void foldOp<DfgMul>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMul(lhs, rhs); }
template <> void foldOp<DfgMulS>       (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMulS(lhs, rhs); }
template <> void foldOp<DfgNeq>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opNeq(lhs, rhs); }
template <> void foldOp<DfgOr>         (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opOr(lhs, rhs); }
template <> void foldOp<DfgPow>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPow(lhs, rhs); }
template <> void foldOp<DfgPowSS>      (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowSS(lhs, rhs); }
template <> void foldOp<DfgPowSU>      (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowSU(lhs, rhs); }
template <> void foldOp<DfgPowUS>      (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowUS(lhs, rhs); }
template <> void foldOp<DfgReplicate>  (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opRepl(lhs, rhs); }
template <> void foldOp<DfgShiftL>     (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftL(lhs, rhs); }
template <> void foldOp<DfgShiftR>     (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftR(lhs, rhs); }
template <> void foldOp<DfgShiftRS>    (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftRS(lhs, rhs, lhs.width()); }
template <> void foldOp<DfgSub>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opSub(lhs, rhs); }
template <> void foldOp<DfgXor>        (V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXor(lhs, rhs); }
}
// clang-format on

class V3DfgPeephole final : public DfgVisitor {
    // TYPES
    struct VertexInfo final {
        size_t m_workListIndex = 0;  // Position of this vertx m_workList (0 means not in list)
        size_t m_iterListIndex = 0;  // Position of this vertx m_iterList (0 means not in list)
        size_t m_generation = 0;  // Generation number of this vertex - for uniqueness check
        size_t m_id = 0;  // Unique vertex ID (0 means unassigned) - for sorting
    };

    // STATE
    DfgGraph& m_dfg;  // The DfgGraph being visited
    V3DfgPeepholeContext& m_ctx;  // The config structure
    const DfgDataType& m_bitDType = DfgDataType::packed(1);  // Common, so grab it up front
    std::vector<DfgVertex*> m_workList;  // List of vertices processed in current interation
    std::vector<DfgVertex*> m_iterList;  // Vertices to start from on next iteration
    DfgUserMap<VertexInfo> m_vInfo = m_dfg.makeUserMap<VertexInfo>();  // Map to VertexInfo
    V3DfgCache m_cache{m_dfg};  // Vertex cache to avoid creating redundant vertices
    DfgVertex* m_vtxp = nullptr;  // Currently considered vertex
    size_t m_currentGeneration = 0;  // Current generation number
    size_t m_lastId = 0;  // Last unique vertex ID assigned

    // STATIC STATE
    static V3DebugBisect s_debugBisect;  // Debug aid

#define APPLYING(id) if (checkApplying(VDfgPeepholePattern::id))

    // METHODS
    bool checkApplying(VDfgPeepholePattern id) {
        if (VL_UNLIKELY(!m_ctx.m_enabled[id] || s_debugBisect.isStopped())) return false;
        UINFO(9, "Applying DFG pattern " << id.ascii());
        ++m_ctx.m_count[id];
        return true;
    }

    void incrementGeneration() {
        ++m_currentGeneration;
        // TODO: could sweep on overflow
    }

    void addToWorkList(DfgVertex* vtxp) {
        VertexInfo& vInfo = m_vInfo[*vtxp];
        // If already on work list, ignore
        if (vInfo.m_workListIndex) return;
        // Add to work list
        vInfo.m_workListIndex = m_workList.size();
        m_workList.push_back(vtxp);
    }

    void removeFromWorkList(DfgVertex* vtxp) {
        VertexInfo& vInfo = m_vInfo[*vtxp];
        // m_workList[0] is always nullptr, fine to assign same here
        m_workList[vInfo.m_workListIndex] = nullptr;
        vInfo.m_workListIndex = 0;
    }

    void addToIterList(DfgVertex* vtxp) {
        VertexInfo& vInfo = m_vInfo[*vtxp];
        // If already on iter list, ignore
        if (vInfo.m_iterListIndex) return;
        // Add to iter list
        vInfo.m_iterListIndex = m_iterList.size();
        m_iterList.push_back(vtxp);
    }

    void removeFromIterList(DfgVertex* vtxp) {
        VertexInfo& vInfo = m_vInfo[*vtxp];
        // m_iterList[0] is always nullptr, fine to assign same here
        m_iterList[vInfo.m_iterListIndex] = nullptr;
        vInfo.m_iterListIndex = 0;
    }

    void deleteVertex(DfgVertex* vtxp) {
        UASSERT_OBJ(!m_vInfo[vtxp].m_workListIndex, vtxp, "Deleted Vertex is in work list");
        UASSERT_OBJ(!vtxp->hasSinks(), vtxp, "Should not delete used vertex");

        // Invalidate cache entry
        m_cache.invalidate(vtxp);

        // It might be in the iter list, remove it
        removeFromIterList(vtxp);

        // Gather source vertices - they might be duplicates, make unique using generation number
        incrementGeneration();
        std::vector<DfgVertex*> srcps;
        srcps.reserve(vtxp->nInputs());
        vtxp->foreachSource([&](DfgVertex& src) {
            // If it's a variable, add to work list to see if it became redundant
            if (src.is<DfgVertexVar>()) {
                addToWorkList(&src);
                return false;
            }
            // Gather unique sources
            VertexInfo& vInfo = m_vInfo[src];
            if (vInfo.m_generation != m_currentGeneration) srcps.push_back(&src);
            vInfo.m_generation = m_currentGeneration;
            return false;
        });

        // This pass only removes variables that are either not driven in this graph,
        // or are not observable outside the graph. If there is also no external write
        // to the variable and no references in other graph then delete the Ast var too.
        const DfgVertexVar* const varp = vtxp->cast<DfgVertexVar>();
        if (varp && !varp->isVolatile() && !varp->hasDfgRefs()) {
            AstNode* const nodep = varp->nodep();
            VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
            m_ctx.m_deleteps.push_back(nodep);
        } else {
            VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
        }

        // Partition sources into used/unused after removing the vertex
        const auto mid
            = std::stable_partition(srcps.begin(), srcps.end(), [](DfgVertex* srcp) {  //
                  return srcp->hasSinks();
              });

        // Add used sources to the iter list - their sinks have changed
        for (auto it = srcps.begin(); it != mid; ++it) addToIterList(*it);

        // Recursively delete unused sources
        for (auto it = mid; it != srcps.end(); ++it) {
            // Remove from work list
            removeFromWorkList(*it);
            // Delete vertex
            deleteVertex(*it);
        }
    }

    // Replace 'm_vtxp' with the given vertex
    void replace(DfgVertex* resp) {
        // Should not be in the work list
        UASSERT_OBJ(!m_vInfo[m_vtxp].m_workListIndex, m_vtxp, "Replaced Vertex is in work list");

        // Debug bisect check
        const auto debugCallback = [&]() -> void {
            UINFO(0, "Problematic DfgPeephole replacement: " << m_vtxp << " -> " << resp);
            m_dfg.sourceCone({m_vtxp, resp});
            const auto cone = m_dfg.sourceCone({m_vtxp, resp});
            m_dfg.dumpDotFilePrefixed("peephole-broken", [&](const DfgVertex& v) {  //
                return cone->count(&v);
            });
        };
        if (VL_UNLIKELY(s_debugBisect.stop(debugCallback))) return;

        // Add sources of the original vertex to the iter list - their sinks are changing
        m_vtxp->foreachSource([&](DfgVertex& src) {
            addToIterList(&src);
            return false;
        });

        // Remove sinks of the original vertex from the cache - their inputs are changing
        m_vtxp->foreachSink([&](DfgVertex& dst) {
            m_cache.invalidate(&dst);
            return false;
        });
        // Replace vertex with the replacement
        m_vtxp->replaceWith(resp);
        // Re-cache all sinks of the replacement
        resp->foreachSink([&](DfgVertex& dst) {
            m_cache.cache(&dst);
            return false;
        });

        // Original vertex is now unused, so delete it
        deleteVertex(m_vtxp);

        // Add new vertex to iter list to consider neighborhood
        addToIterList(resp);
        // Add new vertex and sinks to work list as likely to match
        addToWorkList(resp);
        resp->foreachSink([&](DfgVertex& dst) {
            addToWorkList(&dst);
            return false;
        });
    }

    // Create a 32-bit DfgConst vertex
    DfgConst* makeI32(FileLine* flp, uint32_t val) { return new DfgConst{m_dfg, flp, 32, val}; }

    // Create a DfgConst vertex with the given width and value zero
    DfgConst* makeZero(FileLine* flp, uint32_t width) {
        return new DfgConst{m_dfg, flp, width, 0};
    }

    // Create a DfgConst vertex with the given width and value all ones
    DfgConst* makeOnes(FileLine* flp, uint32_t width) {
        DfgConst* const resp = makeZero(flp, width);
        resp->num().setAllBits1();
        return resp;
    }

    // Create a new vertex of the given type
    template <typename Vertex, typename... Operands>
    Vertex* make(FileLine* flp, const DfgDataType& dtype, Operands... operands) {
        // Find or create an equivalent vertex
        Vertex* const vtxp = m_cache.getOrCreate<Vertex, Operands...>(flp, dtype, operands...);
        // Sanity check
        UASSERT_OBJ(vtxp->dtype() == dtype, vtxp, "Vertex dtype mismatch");
        if (VL_UNLIKELY(v3Global.opt.debugCheck())) vtxp->typeCheck(m_dfg);
        // Assign vertex ID
        VertexInfo& vInfo = m_vInfo[vtxp];
        if (!vInfo.m_id) vInfo.m_id = ++m_lastId;
        // Add to work list
        addToWorkList(vtxp);
        // Return new node
        return vtxp;
    }

    // Same as above, but 'flp' and 'dtypep' are taken from the given example vertex
    template <typename Vertex, typename... Operands>
    Vertex* make(const DfgVertex* examplep, Operands... operands) {
        return make<Vertex>(examplep->fileline(), examplep->dtype(), operands...);
    }

    // Check two vertex are the same, or the same constant value
    static bool isSame(const DfgVertex* ap, const DfgVertex* bp) {
        if (ap == bp) return true;
        if (ap->dtype() != bp->dtype()) return false;
        const DfgConst* const aConstp = ap->cast<DfgConst>();
        if (!aConstp) return false;
        const DfgConst* const bConstp = bp->cast<DfgConst>();
        if (!bConstp) return false;
        return aConstp->num().isCaseEq(bConstp->num());
    }

    static bool isZero(const DfgVertex* vtxp) {
        if (const DfgConst* const constp = vtxp->cast<DfgConst>()) return constp->isZero();
        return false;
    }

    static bool isOnes(const DfgVertex* vtxp) {
        if (const DfgConst* const constp = vtxp->cast<DfgConst>()) return constp->isOnes();
        return false;
    }

    static bool isEqOne(const DfgVertex* vtxp) {
        if (const DfgConst* const constp = vtxp->cast<DfgConst>()) return constp->num().isEqOne();
        return false;
    }

    static bool areAdjacent(uint32_t& lsb, const DfgSel* lSelp, const DfgSel* rSelp) {
        if (!isSame(lSelp->srcp(), rSelp->srcp())) return false;
        if (lSelp->lsb() + lSelp->width() == rSelp->lsb()) {
            lsb = lSelp->lsb();
            return true;
        }
        if (lSelp->lsb() == rSelp->lsb() + rSelp->width()) {
            lsb = rSelp->lsb();
            return true;
        }
        return false;
    }

    // Note: If any of the following transformers return true, then the vertex was replaced and the
    // caller must not do any further changes, so the caller must check the return value, otherwise
    // there will be hard to debug issues.

    // Constant fold unary vertex, return true if folded
    template <typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool foldUnary(Vertex* const vtxp) {
        static_assert(std::is_base_of<DfgVertexUnary, Vertex>::value, "Must invoke on unary");
        static_assert(std::is_final<Vertex>::value, "Must invoke on final class");
        if (DfgConst* const srcp = vtxp->srcp()->template cast<DfgConst>()) {
            APPLYING(FOLD_UNARY) {
                DfgConst* const resultp = makeZero(vtxp->fileline(), vtxp->width());
                foldOp<Vertex>(resultp->num(), srcp->num());
                replace(resultp);
                return true;
            }
        }
        return false;
    }

    // Constant fold binary vertex, return true if folded
    template <typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool foldBinary(Vertex* const vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value, "Must invoke on binary");
        static_assert(std::is_final<Vertex>::value, "Must invoke on final class");
        if (DfgConst* const lhsp = vtxp->inputp(0)->template cast<DfgConst>()) {
            if (DfgConst* const rhsp = vtxp->inputp(1)->template cast<DfgConst>()) {
                APPLYING(FOLD_BINARY) {
                    DfgConst* const resultp = makeZero(vtxp->fileline(), vtxp->width());
                    foldOp<Vertex>(resultp->num(), lhsp->num(), rhsp->num());
                    replace(resultp);
                    return true;
                }
            }
        }
        return false;
    }

    // Transformations that apply to all associative binary vertices.
    // Returns true if vtxp was replaced.
    template <typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool associativeBinary(Vertex* const vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value, "Must invoke on binary");
        static_assert(std::is_final<Vertex>::value, "Must invoke on final class");

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        DfgConst* const lConstp = lhsp->cast<DfgConst>();
        DfgConst* const rConstp = rhsp->cast<DfgConst>();

        if (lConstp && rConstp) {
            APPLYING(FOLD_ASSOC_BINARY) {
                DfgConst* const resultp = makeZero(flp, vtxp->width());
                foldOp<Vertex>(resultp->num(), lConstp->num(), rConstp->num());
                replace(resultp);
                return true;
            }
        }

        if (lConstp) {
            if (Vertex* const rVtxp = rhsp->cast<Vertex>()) {
                if (DfgConst* const rlConstp = rVtxp->lhsp()->template cast<DfgConst>()) {
                    APPLYING(FOLD_ASSOC_BINARY_LHS_OF_RHS) {
                        // Fold constants
                        const uint32_t width = std::is_same<DfgConcat, Vertex>::value
                                                   ? lConstp->width() + rlConstp->width()
                                                   : vtxp->width();
                        DfgConst* const constp = makeZero(flp, width);
                        foldOp<Vertex>(constp->num(), lConstp->num(), rlConstp->num());

                        // Replace vertex
                        replace(make<Vertex>(vtxp, constp, rVtxp->rhsp()));
                        return true;
                    }
                }
            }
        }

        if (rConstp) {
            if (Vertex* const lVtxp = lhsp->cast<Vertex>()) {
                if (DfgConst* const lrConstp = lVtxp->rhsp()->template cast<DfgConst>()) {
                    APPLYING(FOLD_ASSOC_BINARY_RHS_OF_LHS) {
                        // Fold constants
                        const uint32_t width = std::is_same<DfgConcat, Vertex>::value
                                                   ? lrConstp->width() + rConstp->width()
                                                   : vtxp->width();
                        DfgConst* const constp = makeZero(flp, width);
                        foldOp<Vertex>(constp->num(), lrConstp->num(), rConstp->num());

                        // Replace vertex
                        replace(make<Vertex>(vtxp, lVtxp->lhsp(), constp));
                        return true;
                    }
                }
            }
        }

        // Make associative trees right leaning to reduce pattern variations, and for better CSE
        if (Vertex* const alhsp = vtxp->lhsp()->template cast<Vertex>()) {
            if (!alhsp->hasMultipleSinks()) {
                DfgVertex* const ap = alhsp->lhsp();
                DfgVertex* const bp = alhsp->rhsp();
                DfgVertex* const cp = vtxp->rhsp();
                // Only do this if the rhs is not th same as the operands of the LHS, otherwise
                // SWAP_SIDE_IN_COMMUTATIVE_BINARY can get in a loop with this pattern.
                if (ap != cp && bp != cp) {
                    APPLYING(RIGHT_LEANING_ASSOC) {
                        // Rotate the expression tree rooted at 'vtxp' to the right,
                        // producing a right-leaning tree

                        // Concatenation dtypes need adjusting, other assoc vertices preserve types
                        const DfgDataType& childDType
                            = std::is_same<Vertex, DfgConcat>::value
                                  ? DfgDataType::packed(bp->width() + cp->width())
                                  : vtxp->dtype();

                        Vertex* const bcp = make<Vertex>(vtxp->fileline(), childDType, bp, cp);
                        replace(make<Vertex>(alhsp->fileline(), vtxp->dtype(), ap, bcp));
                        return true;
                    }
                }
            }
        }

        // Attempt to reuse associative binary expressions if hey already exist, e.g.:
        // '(a OP (b OP c))' -> '(a OP b) OP c', iff '(a OP b)' already exists, or
        // '(a OP c) OP b' iff '(a OP c)' already exists and the vertex is commutative.
        // Only do this is 'b OP c' has a single use and can subsequently be removed,
        // otherwise there is no improvement.
        if (!rhsp->hasMultipleSinks()) {
            if (Vertex* rVtxp = rhsp->template cast<Vertex>()) {
                DfgVertex* const rlVtxp = rVtxp->lhsp();
                DfgVertex* const rrVtxp = rVtxp->rhsp();

                const DfgDataType& dtype
                    = std::is_same<Vertex, DfgConcat>::value
                          ? DfgDataType::packed(lhsp->width() + rlVtxp->width())
                          : vtxp->dtype();

                if (Vertex* const existingp = m_cache.get<Vertex>(dtype, lhsp, rlVtxp)) {
                    UASSERT_OBJ(existingp->hasSinks(), vtxp, "Existing vertex should be used");
                    if (existingp != rhsp) {
                        APPLYING(REUSE_ASSOC_BINARY_LHS_WITH_LHS_OF_RHS) {
                            replace(make<Vertex>(vtxp, existingp, rrVtxp));
                            return true;
                        }
                    }
                }
                // Concat is not commutative
                if VL_CONSTEXPR_CXX17 (!std::is_same<Vertex, DfgConcat>::value) {
                    if (Vertex* const existingp = m_cache.get<Vertex>(dtype, lhsp, rrVtxp)) {
                        UASSERT_OBJ(existingp->hasSinks(), vtxp, "Existing vertex should be used");
                        if (existingp != rhsp) {
                            APPLYING(REUSE_ASSOC_BINARY_LHS_WITH_RHS_OF_RHS) {
                                replace(make<Vertex>(vtxp, existingp, rlVtxp));
                                return true;
                            }
                        }
                    }
                }
            }
        }

        return false;
    }

    // Transformations that apply to all commutative binary vertices
    template <typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool commutativeBinary(Vertex* const vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Vertex>::value, "Must invoke on binary");
        static_assert(std::is_final<Vertex>::value, "Must invoke on final class");

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        // If constant LHS, push through cond if used once. (Enables branch combining)
        if (DfgConst* const lConstp = lhsp->cast<DfgConst>()) {
            if (DfgCond* const rCondp = rhsp->cast<DfgCond>()) {
                if (!rCondp->hasMultipleSinks()) {
                    APPLYING(PUSH_COMMUTATIVE_BINARY_THROUGH_COND) {
                        DfgVertex* const tp = make<Vertex>(vtxp, lConstp, rCondp->thenp());
                        DfgVertex* const ep = make<Vertex>(vtxp, lConstp, rCondp->elsep());
                        replace(make<DfgCond>(vtxp, rCondp->condp(), tp, ep));
                        return true;
                    }
                }
            }
            return false;
        }

        // Ensure Const is on left-hand side to simplify other patterns
        {
            const bool lIsConst = lhsp->is<DfgConst>();
            const bool rIsConst = rhsp->is<DfgConst>();
            if (lIsConst != rIsConst) {
                if (rIsConst) {
                    APPLYING(SWAP_CONST_IN_COMMUTATIVE_BINARY) {
                        replace(make<Vertex>(vtxp, rhsp, lhsp));
                        return true;
                    }
                }
                return false;
            }
        }

        // Ensure Not is on the left-hand side to simplify other patterns
        {
            const bool lIsNot = lhsp->is<DfgNot>();
            const bool rIsNot = rhsp->is<DfgNot>();
            if (lIsNot != rIsNot) {
                if (rIsNot) {
                    APPLYING(SWAP_NOT_IN_COMMUTATIVE_BINARY) {
                        replace(make<Vertex>(vtxp, rhsp, lhsp));
                        return true;
                    }
                }
                return false;
            }
        }

        // Ensure same vertex is on the right-hand side to simplify other patterns
        {
            const bool lIsSame = lhsp->is<Vertex>();
            const bool rIsSame = rhsp->is<Vertex>();
            if (lIsSame != rIsSame) {
                if (lIsSame) {
                    APPLYING(SWAP_SAME_IN_COMMUTATIVE_BINARY) {
                        replace(make<Vertex>(vtxp, rhsp, lhsp));
                        return true;
                    }
                }
                return false;
            }
        }

        // Otherwise put sides in order based on unique iD, this makes
        // 'a op b' and 'b op a' end up the same for better combining.
        {
            const VertexInfo& lInfo = m_vInfo[lhsp];
            const VertexInfo& rInfo = m_vInfo[rhsp];
            if (lInfo.m_id > rInfo.m_id) {
                APPLYING(SWAP_SIDE_IN_COMMUTATIVE_BINARY) {
                    replace(make<Vertex>(vtxp, rhsp, lhsp));
                    return true;
                }
            }
        }

        return false;
    }

    // Transformations that apply to all distributive and associative binary
    // vertices 'Other' is the type that is distributive over 'Vertex',
    // that is: a Other (b Vertex c) == (a Other b) Vertex (a Other c)
    template <typename Other, typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool distributiveAndAssociativeBinary(Vertex* vtxp) {
        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        if (!lhsp->hasMultipleSinks() && !rhsp->hasMultipleSinks()) {
            // Convert '(a Other b) Vertex (a Other c)' and associative
            // variations to 'a Other (b Vertex c)'
            if (Other* const lp = lhsp->cast<Other>()) {
                if (Other* const rp = rhsp->cast<Other>()) {
                    DfgVertex* const llp = lp->lhsp();
                    DfgVertex* const lrp = lp->rhsp();
                    DfgVertex* const rlp = rp->lhsp();
                    DfgVertex* const rrp = rp->rhsp();
                    DfgVertex* ap = nullptr;
                    DfgVertex* bp = nullptr;
                    DfgVertex* cp = nullptr;
                    if (llp == rlp) {
                        ap = llp;
                        bp = lrp;
                        cp = rrp;
                    } else if (llp == rrp) {
                        ap = llp;
                        bp = lrp;
                        cp = rlp;
                    } else if (lrp == rlp) {
                        ap = lrp;
                        bp = llp;
                        cp = rrp;
                    } else if (lrp == rrp) {
                        ap = lrp;
                        bp = llp;
                        cp = rlp;
                    }
                    if (ap) {
                        APPLYING(REPLACE_DISTRIBUTIVE_BINARY) {
                            replace(make<Other>(vtxp, ap, make<Vertex>(lhsp, bp, cp)));
                            return true;
                        }
                    }
                }
            }
        }

        return false;
    }

    // Bitwise operation with one side Const, and the other side a Concat
    template <typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool
    tryPushBitwiseOpThroughConcat(Vertex* const vtxp, DfgConst* constp, DfgConcat* concatp) {
        FileLine* const flp = vtxp->fileline();

        // If at least one of the sides of the Concat constant, or width 1 (i.e.: can be
        // further simplified), then push the Vertex past the Concat
        if (concatp->lhsp()->is<DfgConst>() || concatp->rhsp()->is<DfgConst>()  //
            || concatp->lhsp()->dtype() == m_bitDType || concatp->rhsp()->dtype() == m_bitDType) {
            APPLYING(PUSH_BITWISE_OP_THROUGH_CONCAT) {
                const uint32_t width = concatp->width();
                const DfgDataType& lDtype = concatp->lhsp()->dtype();
                const DfgDataType& rDtype = concatp->rhsp()->dtype();
                const uint32_t lWidth = lDtype.size();
                const uint32_t rWidth = rDtype.size();

                // The new Lhs vertex
                DfgConst* const newLhsConstp = makeZero(constp->fileline(), lWidth);
                newLhsConstp->num().opSel(constp->num(), width - 1, rWidth);
                Vertex* const newLhsp = make<Vertex>(flp, lDtype, newLhsConstp, concatp->lhsp());

                // The new Rhs vertex
                DfgConst* const newRhsConstp = makeZero(constp->fileline(), rWidth);
                newRhsConstp->num().opSel(constp->num(), rWidth - 1, 0);
                Vertex* const newRhsp = make<Vertex>(flp, rDtype, newRhsConstp, concatp->rhsp());

                // Replace this vertex
                replace(make<DfgConcat>(concatp, newLhsp, newRhsp));
                return true;
            }
        }
        return false;
    }

    template <typename Vertex>
    VL_ATTR_WARN_UNUSED_RESULT bool
    tryPushCompareOpThroughConcat(Vertex* const vtxp, DfgConst* constp, DfgConcat* concatp) {
        FileLine* const flp = vtxp->fileline();

        // If at least one of the sides of the Concat is constant, then push the Vertex past
        // the Concat
        if (concatp->lhsp()->is<DfgConst>() || concatp->rhsp()->is<DfgConst>()) {
            APPLYING(PUSH_COMPARE_OP_THROUGH_CONCAT) {
                const uint32_t width = concatp->width();
                const uint32_t lWidth = concatp->lhsp()->width();
                const uint32_t rWidth = concatp->rhsp()->width();

                // The new Lhs vertex
                DfgConst* const newLhsConstp = makeZero(constp->fileline(), lWidth);
                newLhsConstp->num().opSel(constp->num(), width - 1, rWidth);
                Vertex* const newLhsp
                    = make<Vertex>(flp, m_bitDType, newLhsConstp, concatp->lhsp());

                // The new Rhs vertex
                DfgConst* const newRhsConstp = makeZero(constp->fileline(), rWidth);
                newRhsConstp->num().opSel(constp->num(), rWidth - 1, 0);
                Vertex* const newRhsp
                    = make<Vertex>(flp, m_bitDType, newRhsConstp, concatp->rhsp());

                // The replacement Vertex
                DfgVertexBinary* const resp
                    = std::is_same<Vertex, DfgEq>::value
                          ? make<DfgAnd>(concatp->fileline(), m_bitDType, newLhsp, newRhsp)
                          : nullptr;
                UASSERT_OBJ(resp, vtxp,
                            "Unhandled vertex type in 'tryPushCompareOpThroughConcat': "
                                << vtxp->typeName());

                // Replace this vertex
                replace(resp);
                return true;
            }
        }
        return false;
    }

    template <typename Bitwise>
    VL_ATTR_WARN_UNUSED_RESULT bool tryPushBitwiseOpThroughReductions(Bitwise* const vtxp) {
        using Reduction = BitwiseToReduction<Bitwise>;

        if (Reduction* const lRedp = vtxp->lhsp()->template cast<Reduction>()) {
            if (Reduction* const rRedp = vtxp->rhsp()->template cast<Reduction>()) {
                DfgVertex* const lSrcp = lRedp->srcp();
                DfgVertex* const rSrcp = rRedp->srcp();
                if (lSrcp->dtype() == rSrcp->dtype() && lSrcp->width() <= VL_QUADSIZE
                    && !lSrcp->is<DfgConcat>() && !rSrcp->is<DfgConcat>()
                    && !lSrcp->hasMultipleSinks() && !rSrcp->hasMultipleSinks()) {
                    APPLYING(PUSH_BITWISE_THROUGH_REDUCTION) {
                        FileLine* const flp = vtxp->fileline();
                        Bitwise* const bwp = make<Bitwise>(flp, lSrcp->dtype(), lSrcp, rSrcp);
                        replace(make<Reduction>(flp, m_bitDType, bwp));
                        return true;
                    }
                }
            }
        }

        return false;
    }

    template <typename Bitwise>
    VL_ATTR_WARN_UNUSED_RESULT bool tryReplaceBitwiseWithReduction(Bitwise* vtxp) {
        UASSERT_OBJ(vtxp->width() == 1, vtxp, "Width must be 1");
        using Reduction = BitwiseToReduction<Bitwise>;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (DfgSel* const lSelp = lhsp->template cast<DfgSel>()) {
            DfgSel* rSelp = rhsp->template cast<DfgSel>();
            DfgVertex* extrap = nullptr;
            if (!rSelp) {
                if (Bitwise* const rBitwisep = rhsp->template cast<Bitwise>()) {
                    rSelp = rBitwisep->lhsp()->template cast<DfgSel>();
                    extrap = rBitwisep->rhsp();
                }
            }
            if (rSelp) {
                uint32_t lsb = 0;
                if (areAdjacent(lsb, lSelp, rSelp)) {
                    APPLYING(REPLACE_BITWISE_OF_SELS_WITH_REDUCTION) {
                        const DfgDataType& dtype
                            = DfgDataType::packed(lSelp->width() + rSelp->width());
                        DfgSel* const newSelp
                            = make<DfgSel>(lSelp->fileline(), dtype, lSelp->srcp(), lsb);
                        DfgVertex* resp = make<Reduction>(vtxp, newSelp);
                        if (extrap) resp = make<Bitwise>(vtxp, resp, extrap);
                        replace(resp);
                        return true;
                    }
                }
            }
        }

        if (Reduction* const lRedp = lhsp->template cast<Reduction>()) {
            Reduction* rRedp = rhsp->template cast<Reduction>();
            DfgVertex* extrap = nullptr;
            if (!rRedp) {
                if (Bitwise* const rBitwisep = rhsp->template cast<Bitwise>()) {
                    rRedp = rBitwisep->lhsp()->template cast<Reduction>();
                    extrap = rBitwisep->rhsp();
                }
            }
            if (rRedp) {
                if (DfgSel* const lSelp = lRedp->srcp()->template cast<DfgSel>()) {
                    if (DfgSel* const rSelp = rRedp->srcp()->template cast<DfgSel>()) {
                        uint32_t lsb = 0;
                        if (areAdjacent(lsb, lSelp, rSelp)) {
                            APPLYING(REPLACE_BITWISE_OF_REDUCTION_OF_SELS_WITH_REDUCTION) {
                                const DfgDataType& dtype
                                    = DfgDataType::packed(lSelp->width() + rSelp->width());
                                DfgSel* const newSelp
                                    = make<DfgSel>(lSelp->fileline(), dtype, lSelp->srcp(), lsb);
                                DfgVertex* resp = make<Reduction>(vtxp, newSelp);
                                if (extrap) resp = make<Bitwise>(vtxp, resp, extrap);
                                replace(resp);
                                return true;
                            }
                        }
                    }
                }
            }
        }

        return false;
    }

    template <typename Reduction>
    VL_ATTR_WARN_UNUSED_RESULT bool optimizeReduction(Reduction* const vtxp) {
        using Bitwise = ReductionToBitwise<Reduction>;

        if (foldUnary(vtxp)) return true;

        DfgVertex* const srcp = vtxp->srcp();
        FileLine* const flp = vtxp->fileline();

        // Reduction of 1-bit value
        if (srcp->dtype() == m_bitDType) {
            APPLYING(REMOVE_WIDTH_ONE_REDUCTION) {
                replace(srcp);
                return true;
            }
        }

        if (DfgCond* const condp = srcp->cast<DfgCond>()) {
            if (condp->thenp()->is<DfgConst>() || condp->elsep()->is<DfgConst>()) {
                APPLYING(PUSH_REDUCTION_THROUGH_COND_WITH_CONST_BRANCH) {
                    // The new 'then' vertex
                    Reduction* const newThenp = make<Reduction>(flp, m_bitDType, condp->thenp());

                    // The new 'else' vertex
                    Reduction* const newElsep = make<Reduction>(flp, m_bitDType, condp->elsep());

                    // The replacement Cond vertex
                    DfgCond* const newCondp = make<DfgCond>(condp->fileline(), m_bitDType,
                                                            condp->condp(), newThenp, newElsep);

                    // Replace this vertex
                    replace(newCondp);
                    return true;
                }
            }
        }

        if (DfgConcat* const concatp = srcp->cast<DfgConcat>()) {
            if (concatp->lhsp()->is<DfgConst>() || concatp->rhsp()->is<DfgConst>()
                || concatp->lhsp()->dtype() == m_bitDType
                || concatp->rhsp()->dtype() == m_bitDType) {
                APPLYING(PUSH_REDUCTION_THROUGH_CONCAT) {
                    // Reduce the parts of the concatenation
                    Reduction* const lRedp
                        = make<Reduction>(concatp->fileline(), m_bitDType, concatp->lhsp());
                    Reduction* const rRedp
                        = make<Reduction>(concatp->fileline(), m_bitDType, concatp->rhsp());

                    // Bitwise reduce the results
                    replace(make<Bitwise>(flp, m_bitDType, lRedp, rRedp));
                    return true;
                }
            }
        }

        if (Bitwise* const bitwisep = vtxp->srcp()->template cast<Bitwise>()) {
            if (!bitwisep->hasMultipleSinks()) {
                if (bitwisep->lhsp()->template is<DfgConcat>()
                    || bitwisep->rhsp()->template is<DfgConcat>()) {
                    APPLYING(PUSH_REDUCTION_THROUGH_BITWISE_OF_CONCAT) {
                        Reduction* const newLhsp
                            = make<Reduction>(flp, m_bitDType, bitwisep->lhsp());
                        Reduction* const newRhsp
                            = make<Reduction>(flp, m_bitDType, bitwisep->rhsp());
                        replace(make<Bitwise>(flp, m_bitDType, newLhsp, newRhsp));
                        return true;
                    }
                }

                if (DfgSel* const lSelp = bitwisep->lhsp()->template cast<DfgSel>()) {
                    if (DfgSel* const rSelp = bitwisep->rhsp()->template cast<DfgSel>()) {
                        uint32_t lsb = 0;
                        if (areAdjacent(lsb, lSelp, rSelp)) {
                            APPLYING(PUSH_REDUCTION_THROUGH_BITWISE_OF_SELS) {
                                const DfgDataType& dtype
                                    = DfgDataType::packed(lSelp->width() + rSelp->width());
                                DfgSel* const newSelp
                                    = make<DfgSel>(lSelp->fileline(), dtype, lSelp->srcp(), lsb);
                                replace(make<Reduction>(vtxp, newSelp));
                                return true;
                            }
                        }
                    }
                }
            }
        }

        return false;
    }

    template <typename Shift>
    VL_ATTR_WARN_UNUSED_RESULT bool optimizeShiftRHS(Shift* const vtxp) {
        static_assert(std::is_base_of<DfgVertexBinary, Shift>::value, "Must invoke on binary");
        static_assert(std::is_final<Shift>::value, "Must invoke on final class");
        if (const DfgConcat* const concatp = vtxp->rhsp()->template cast<DfgConcat>()) {
            if (isZero(concatp->lhsp())) {  // Drop redundant zero extension
                APPLYING(REMOVE_REDUNDANT_ZEXT_ON_RHS_OF_SHIFT) {
                    replace(make<Shift>(vtxp, vtxp->lhsp(), concatp->rhsp()));
                    return true;
                }
            }
        }
        return false;
    }

    // Given an operand of an Add, return the term that could be used for conveting to CountOnes
    // Result is a tulpe of (Vertex, Lsb, Width)
    std::tuple<DfgVertex*, uint32_t, uint32_t> addToCountOnesTerm(DfgVertex* vtxp) {
        if (DfgConcat* const oCatp = vtxp->cast<DfgConcat>()) {
            if (isZero(oCatp->lhsp())) {
                if (DfgCountOnes* const countOnesp = oCatp->rhsp()->cast<DfgCountOnes>()) {
                    // Zero extended count ones
                    if (DfgSel* const selp = countOnesp->srcp()->cast<DfgSel>()) {
                        return {selp->fromp(), selp->lsb(), selp->width()};
                    }
                } else if (DfgSel* const selp = oCatp->rhsp()->cast<DfgSel>()) {
                    // Zero extended single bit select
                    if (selp->dtype() == m_bitDType) {  //
                        return {selp->fromp(), selp->lsb(), selp->width()};
                    }
                }
            }
            return {nullptr, 0, 0};
        }
        if (DfgCountOnes* const countOnesp = vtxp->cast<DfgCountOnes>()) {
            // Simple count ones
            if (DfgSel* const selp = countOnesp->srcp()->cast<DfgSel>()) {
                return {selp->fromp(), selp->lsb(), selp->width()};
            }
            return {nullptr, 0, 0};
        }
        if (DfgSel* const oSelp = vtxp->cast<DfgSel>()) {
            if (oSelp->lsb() == 0) {
                // Truncated count ones
                if (DfgCountOnes* const countOnesp = oSelp->fromp()->cast<DfgCountOnes>()) {
                    // Zero extended count ones
                    if (DfgSel* const selp = countOnesp->srcp()->cast<DfgSel>()) {
                        return {selp->fromp(), selp->lsb(), selp->width()};
                    }
                }
            }
            // Single bit select
            if (oSelp->dtype() == m_bitDType) {  //
                return {oSelp->fromp(), oSelp->lsb(), 1};
            }
            return {nullptr, 0, 0};
        }
        // Altered form of extended MSB
        if (DfgShiftR* const shiftrp = vtxp->cast<DfgShiftR>()) {
            if (DfgConst* const rConstp = shiftrp->rhsp()->cast<DfgConst>()) {
                if (rConstp->toU32() == shiftrp->width() - 1) {
                    return {shiftrp->lhsp(), shiftrp->width() - 1, 1};
                }
            }
            return {nullptr, 0, 0};
        }
        // Not applicable
        return {nullptr, 0, 0};
    }

    // VISIT methods

    void visit(DfgVertex*) override {}

    //=========================================================================
    //  DfgVertexUnary
    //=========================================================================

    void visit(DfgExtend* const vtxp) override {
        if (foldUnary(vtxp)) return;

        // Convert all Extend into Concat with zeros. This simplifies other patterns as they
        // only need to handle Concat, which is more generic, and don't need special cases for
        // Extend.
        APPLYING(REPLACE_EXTEND) {
            DfgVertex* const zerop
                = makeZero(vtxp->fileline(), vtxp->width() - vtxp->srcp()->width());
            replace(make<DfgConcat>(vtxp, zerop, vtxp->srcp()));
            return;
        }
    }

    void visit(DfgExtendS* const vtxp) override {
        if (foldUnary(vtxp)) return;
    }

    void visit(DfgLogNot* const vtxp) override {
        if (foldUnary(vtxp)) return;
    }

    void visit(DfgNegate* const vtxp) override {
        if (foldUnary(vtxp)) return;
    }

    void visit(DfgNot* const vtxp) override {
        if (foldUnary(vtxp)) return;

        // Not of Cond
        if (DfgCond* const condp = vtxp->srcp()->cast<DfgCond>()) {
            // If at least one of the branches are a constant, push the Not past the Cond
            if (condp->thenp()->is<DfgConst>() || condp->elsep()->is<DfgConst>()) {
                APPLYING(PUSH_NOT_THROUGH_COND) {
                    // The new 'then' vertex
                    DfgNot* const newThenp = make<DfgNot>(vtxp, condp->thenp());

                    // The new 'else' vertex
                    DfgNot* const newElsep = make<DfgNot>(vtxp, condp->elsep());

                    // The replacement Cond vertex
                    DfgCond* const newCondp = make<DfgCond>(condp->fileline(), vtxp->dtype(),
                                                            condp->condp(), newThenp, newElsep);

                    // Replace this vertex
                    replace(newCondp);
                    return;
                }
            }
        }

        // Not of Not
        if (DfgNot* const notp = vtxp->srcp()->cast<DfgNot>()) {
            APPLYING(REMOVE_NOT_NOT) {
                replace(notp->srcp());
                return;
            }
        }

        if (!vtxp->srcp()->hasMultipleSinks()) {
            // Not of Eq
            if (DfgEq* const eqp = vtxp->srcp()->cast<DfgEq>()) {
                APPLYING(REPLACE_NOT_EQ) {
                    replace(
                        make<DfgNeq>(eqp->fileline(), vtxp->dtype(), eqp->lhsp(), eqp->rhsp()));
                    return;
                }
            }

            // Not of Neq
            if (DfgNeq* const neqp = vtxp->srcp()->cast<DfgNeq>()) {
                APPLYING(REPLACE_NOT_NEQ) {
                    replace(
                        make<DfgEq>(neqp->fileline(), vtxp->dtype(), neqp->lhsp(), neqp->rhsp()));
                    return;
                }
            }
        }
    }

    void visit(DfgRedOr* const vtxp) override {
        if (optimizeReduction(vtxp)) return;
    }

    void visit(DfgRedAnd* const vtxp) override {
        if (optimizeReduction(vtxp)) return;
    }

    void visit(DfgRedXor* const vtxp) override {
        if (optimizeReduction(vtxp)) return;
    }

    void visit(DfgSel* const vtxp) override {
        DfgVertex* const fromp = vtxp->fromp();

        FileLine* const flp = vtxp->fileline();

        const uint32_t lsb = vtxp->lsb();
        const uint32_t width = vtxp->width();
        const uint32_t msb = lsb + width - 1;

        if (DfgConst* const constp = fromp->cast<DfgConst>()) {
            APPLYING(FOLD_SEL) {
                DfgConst* const resp = makeZero(flp, width);
                resp->num().opSel(constp->num(), msb, lsb);
                replace(resp);
                return;
            }
        }

        // Full width select, replace with the source.
        if (fromp->width() == width) {
            UASSERT_OBJ(lsb == 0, fromp, "Out of range select should have been fixed up earlier");
            APPLYING(REMOVE_FULL_WIDTH_SEL) {
                replace(fromp);
                return;
            }
        }

        // Sel from Concat
        if (DfgConcat* const concatp = fromp->cast<DfgConcat>()) {
            DfgVertex* const lhsp = concatp->lhsp();
            DfgVertex* const rhsp = concatp->rhsp();

            if (msb < rhsp->width()) {
                // If the select is entirely from rhs, then replace with sel from rhs
                APPLYING(REMOVE_SEL_FROM_RHS_OF_CONCAT) {  //
                    replace(make<DfgSel>(vtxp, rhsp, vtxp->lsb()));
                    return;
                }
            } else if (lsb >= rhsp->width()) {
                // If the select is entirely from the lhs, then replace with sel from lhs
                APPLYING(REMOVE_SEL_FROM_LHS_OF_CONCAT) {
                    replace(make<DfgSel>(vtxp, lhsp, lsb - rhsp->width()));
                    return;
                }
            }
        }

        if (DfgReplicate* const repp = fromp->cast<DfgReplicate>()) {
            // If the Sel is wholly into the source of the Replicate, push the Sel through the
            // Replicate and apply it directly to the source of the Replicate.
            const uint32_t srcWidth = repp->srcp()->width();
            if (width <= srcWidth) {
                const uint32_t newLsb = lsb % srcWidth;
                if (newLsb + width <= srcWidth) {
                    APPLYING(PUSH_SEL_THROUGH_REPLICATE) {
                        replace(make<DfgSel>(vtxp, repp->srcp(), newLsb));
                        return;
                    }
                }
            }
        }

        // Sel from Not
        if (DfgNot* const notp = fromp->cast<DfgNot>()) {
            // Replace "Sel from Not" with "Not of Sel"
            if (!notp->hasMultipleSinks()) {
                APPLYING(PUSH_SEL_THROUGH_NOT) {
                    // Make Sel select from source of Not
                    DfgSel* const newSelp = make<DfgSel>(vtxp, notp->srcp(), vtxp->lsb());
                    // Add Not after Sel
                    replace(make<DfgNot>(notp->fileline(), vtxp->dtype(), newSelp));
                    return;
                }
            }
        }

        // Sel from Sel
        if (DfgSel* const selp = fromp->cast<DfgSel>()) {
            APPLYING(REPLACE_SEL_FROM_SEL) {
                // Select from the source of the source Sel with adjusted LSB
                replace(make<DfgSel>(vtxp, selp->fromp(), lsb + selp->lsb()));
                return;
            }
        }

        // Sel from Cond
        if (DfgCond* const condp = fromp->cast<DfgCond>()) {
            if (!condp->hasMultipleSinks()) {
                APPLYING(PUSH_SEL_THROUGH_COND) {
                    // The new 'then' vertex
                    DfgSel* const newThenp = make<DfgSel>(vtxp, condp->thenp(), lsb);

                    // The new 'else' vertex
                    DfgSel* const newElsep = make<DfgSel>(vtxp, condp->elsep(), lsb);

                    // The replacement Cond vertex
                    DfgCond* const newCondp = make<DfgCond>(condp->fileline(), vtxp->dtype(),
                                                            condp->condp(), newThenp, newElsep);

                    // Replace this vertex
                    replace(newCondp);
                    return;
                }
            }
        }

        // Sel from ShiftL
        if (DfgShiftL* const shiftLp = fromp->cast<DfgShiftL>()) {
            // If selecting bottom bits of left shift, push the Sel before the shift
            if (lsb == 0) {
                UASSERT_OBJ(shiftLp->lhsp()->width() >= width, vtxp, "input of shift narrow");
                APPLYING(PUSH_SEL_THROUGH_SHIFTL) {
                    DfgSel* const newSelp = make<DfgSel>(vtxp, shiftLp->lhsp(), vtxp->lsb());
                    replace(make<DfgShiftL>(vtxp, newSelp, shiftLp->rhsp()));
                    return;
                }
            }
        }

        // Sel from a partial variable or narrowed vertex
        {
            DfgSplicePacked* splicep = fromp->cast<DfgSplicePacked>();
            if (DfgVarPacked* const varp = fromp->cast<DfgVarPacked>()) {
                // Must be a splice, otherwise it would have been inlined
                if (varp->tmpForp() && varp->srcp()) splicep = varp->srcp()->as<DfgSplicePacked>();
            }
            if (splicep) {
                DfgVertex* driverp = nullptr;
                uint32_t driverLsb = 0;
                splicep->foreachDriver([&](DfgVertex& src, const uint32_t dLsb) {
                    const uint32_t dMsb = dLsb + src.width() - 1;
                    // If it does not cover the whole searched bit range, move on
                    if (lsb < dLsb || dMsb < msb) return false;
                    // Save the driver
                    driverp = &src;
                    driverLsb = dLsb;
                    return true;
                });
                if (driverp) {
                    APPLYING(PUSH_SEL_THROUGH_SPLICE) {
                        replace(make<DfgSel>(vtxp, driverp, lsb - driverLsb));
                        return;
                    }
                }
            }
        }
    }

    void visit(DfgMux* const vtxp) override {
        DfgVertex* const fromp = vtxp->fromp();
        DfgVertex* const lsbp = vtxp->lsbp();
        FileLine* const flp = vtxp->fileline();

        if (DfgConst* const lsbConstp = lsbp->cast<DfgConst>()) {
            APPLYING(REPLACE_MUX_WITH_SEL) {
                replace(make<DfgSel>(vtxp, fromp, lsbConstp->num().toUInt()));
                return;
            }
        }

        if (isZero(fromp)) {
            APPLYING(FOLD_MUX_FROM_ZERO) {
                replace(makeZero(flp, vtxp->width()));
                return;
            }
        }

        if (isOnes(fromp)) {
            APPLYING(FOLD_MUX_FROM_ONES) {
                replace(makeOnes(flp, vtxp->width()));
                return;
            }
        }
    }

    //=========================================================================
    //  DfgVertexBinary - bitwise
    //=========================================================================

    void visit(DfgAnd* const vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (isSame(lhsp, rhsp)) {
            APPLYING(REMOVE_AND_WITH_SELF) {
                replace(lhsp);
                return;
            }
        }

        if (associativeBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;

        FileLine* const flp = vtxp->fileline();

        // Bubble pushing (De Morgan)
        if (!lhsp->hasMultipleSinks() || !rhsp->hasMultipleSinks()) {
            if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
                if (DfgNot* const rhsNotp = rhsp->cast<DfgNot>()) {
                    APPLYING(REPLACE_AND_OF_NOT_AND_NOT) {
                        DfgOr* const orp = make<DfgOr>(vtxp, lhsNotp->srcp(), rhsNotp->srcp());
                        replace(make<DfgNot>(vtxp, orp));
                        return;
                    }
                }
                if (DfgNeq* const rhsNeqp = rhsp->cast<DfgNeq>()) {
                    APPLYING(REPLACE_AND_OF_NOT_AND_NEQ) {
                        DfgEq* const newRhsp = make<DfgEq>(rhsp, rhsNeqp->lhsp(), rhsNeqp->rhsp());
                        DfgOr* const orp = make<DfgOr>(vtxp, lhsNotp->srcp(), newRhsp);
                        replace(make<DfgNot>(vtxp, orp));
                        return;
                    }
                }
            }
        }

        if (DfgConst* const lConstp = lhsp->cast<DfgConst>()) {
            if (lConstp->isZero()) {
                APPLYING(REPLACE_AND_WITH_ZERO) {
                    replace(lConstp);
                    return;
                }
            }

            if (lConstp->isOnes()) {
                APPLYING(REMOVE_AND_WITH_ONES) {
                    replace(rhsp);
                    return;
                }
            }

            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushBitwiseOpThroughConcat(vtxp, lConstp, rhsConcatp)) return;
            }
        }

        if (distributiveAndAssociativeBinary<DfgOr, DfgAnd>(vtxp)) return;

        if (tryPushBitwiseOpThroughReductions(vtxp)) return;

        if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
            // ~A & A is all zeroes
            if (lhsNotp->srcp() == rhsp) {
                APPLYING(REPLACE_CONTRADICTORY_AND) {
                    replace(makeZero(flp, vtxp->width()));
                    return;
                }
            }

            // ~A & (A & _) or ~A & (_ & A) is all zeroes
            if (DfgAnd* const rhsAndp = rhsp->cast<DfgAnd>()) {
                if (lhsNotp->srcp() == rhsAndp->lhsp() || lhsNotp->srcp() == rhsAndp->rhsp()) {
                    APPLYING(REPLACE_CONTRADICTORY_AND_3) {
                        replace(makeZero(flp, vtxp->width()));
                        return;
                    }
                }
            }
        }

        if (vtxp->dtype() == m_bitDType) {
            if (tryReplaceBitwiseWithReduction(vtxp)) return;
        }
    }

    void visit(DfgOr* const vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (isSame(lhsp, rhsp)) {
            APPLYING(REMOVE_OR_WITH_SELF) {
                replace(lhsp);
                return;
            }
        }

        if (associativeBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;

        FileLine* const flp = vtxp->fileline();

        // Bubble pushing (De Morgan)
        if (!lhsp->hasMultipleSinks() || !rhsp->hasMultipleSinks()) {
            if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
                if (DfgNot* const rhsNotp = rhsp->cast<DfgNot>()) {
                    APPLYING(REPLACE_OR_OF_NOT_AND_NOT) {
                        DfgAnd* const andp = make<DfgAnd>(vtxp, lhsNotp->srcp(), rhsNotp->srcp());
                        replace(make<DfgNot>(vtxp, andp));
                        return;
                    }
                }
                if (DfgNeq* const rhsNeqp = rhsp->cast<DfgNeq>()) {
                    APPLYING(REPLACE_OR_OF_NOT_AND_NEQ) {
                        DfgEq* const newRhsp = make<DfgEq>(rhsp, rhsNeqp->lhsp(), rhsNeqp->rhsp());
                        DfgAnd* const andp = make<DfgAnd>(vtxp, lhsNotp->srcp(), newRhsp);
                        replace(make<DfgNot>(vtxp, andp));
                        return;
                    }
                }
            }
        }

        if (DfgConcat* const lhsConcatp = lhsp->cast<DfgConcat>()) {
            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (lhsConcatp->lhsp()->dtype() == rhsConcatp->lhsp()->dtype()) {
                    if (isZero(lhsConcatp->lhsp()) && isZero(rhsConcatp->rhsp())) {
                        APPLYING(REPLACE_OR_OF_CONCAT_ZERO_LHS_AND_CONCAT_RHS_ZERO) {
                            replace(make<DfgConcat>(vtxp, rhsConcatp->lhsp(), lhsConcatp->rhsp()));
                            return;
                        }
                    }
                    if (isZero(lhsConcatp->rhsp()) && isZero(rhsConcatp->lhsp())) {
                        APPLYING(REPLACE_OR_OF_CONCAT_LHS_ZERO_AND_CONCAT_ZERO_RHS) {
                            replace(make<DfgConcat>(vtxp, lhsConcatp->lhsp(), rhsConcatp->rhsp()));
                            return;
                        }
                    }
                }
            }
        }

        if (DfgConst* const lConstp = lhsp->cast<DfgConst>()) {
            if (lConstp->isZero()) {
                APPLYING(REMOVE_OR_WITH_ZERO) {
                    replace(rhsp);
                    return;
                }
            }

            if (lConstp->isOnes()) {
                APPLYING(REPLACE_OR_WITH_ONES) {
                    replace(lhsp);
                    return;
                }
            }

            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushBitwiseOpThroughConcat(vtxp, lConstp, rhsConcatp)) return;
            }
        }

        if (distributiveAndAssociativeBinary<DfgAnd, DfgOr>(vtxp)) return;

        if (tryPushBitwiseOpThroughReductions(vtxp)) return;

        if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
            // ~A | A is all ones
            if (lhsNotp->srcp() == rhsp) {
                APPLYING(REPLACE_TAUTOLOGICAL_OR) {
                    DfgConst* const resp = makeZero(flp, vtxp->width());
                    resp->num().setAllBits1();
                    replace(resp);
                    return;
                }
            }

            // ~A | (A | _) or ~A | (_ | A) is all ones
            if (DfgOr* const rhsOrp = rhsp->cast<DfgOr>()) {
                if (lhsNotp->srcp() == rhsOrp->lhsp() || lhsNotp->srcp() == rhsOrp->rhsp()) {
                    APPLYING(REPLACE_TAUTOLOGICAL_OR_3) {
                        DfgConst* const resp = makeZero(flp, vtxp->width());
                        resp->num().setAllBits1();
                        replace(resp);
                        return;
                    }
                }
            }
        }

        if (vtxp->dtype() == m_bitDType) {
            if (tryReplaceBitwiseWithReduction(vtxp)) return;
        }
    }

    void visit(DfgXor* const vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (isSame(lhsp, rhsp)) {
            APPLYING(REPLACE_XOR_WITH_SELF) {
                replace(makeZero(vtxp->fileline(), vtxp->width()));
                return;
            }
        }

        if (associativeBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;

        if (DfgConst* const lConstp = lhsp->cast<DfgConst>()) {
            if (lConstp->isZero()) {
                APPLYING(REMOVE_XOR_WITH_ZERO) {
                    replace(rhsp);
                    return;
                }
            }
            if (lConstp->isOnes()) {
                APPLYING(REPLACE_XOR_WITH_ONES) {
                    replace(make<DfgNot>(vtxp, rhsp));
                    return;
                }
            }
            if (DfgConcat* const rConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushBitwiseOpThroughConcat(vtxp, lConstp, rConcatp)) return;
            }
        }

        if (tryPushBitwiseOpThroughReductions(vtxp)) return;

        if (vtxp->dtype() == m_bitDType) {
            if (tryReplaceBitwiseWithReduction(vtxp)) return;
        }
    }

    //=========================================================================
    //  DfgVertexBinary - other
    //=========================================================================

    void visit(DfgAdd* const vtxp) override {
        if (associativeBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isZero(lhsp)) {
            APPLYING(REMOVE_ADD_ZERO) {
                replace(rhsp);
                return;
            }
        }

        const std::tuple<DfgVertex*, uint32_t, uint32_t> lTerm = addToCountOnesTerm(lhsp);
        if (DfgVertex* const lVtxp = std::get<0>(lTerm)) {
            std::tuple<DfgVertex*, uint32_t, uint32_t> rTerm = addToCountOnesTerm(rhsp);
            DfgVertex* extrap = nullptr;
            if (!std::get<0>(rTerm)) {
                if (DfgAdd* const rAddp = rhsp->cast<DfgAdd>()) {
                    rTerm = addToCountOnesTerm(rAddp->lhsp());
                    extrap = rAddp->rhsp();
                }
            }

            if (DfgVertex* const rVtxp = std::get<0>(rTerm)) {
                if (isSame(lVtxp, rVtxp)) {
                    const uint32_t lLsb = std::get<1>(lTerm);
                    const uint32_t rLsb = std::get<1>(rTerm);
                    const uint32_t lWidth = std::get<2>(lTerm);
                    const uint32_t rWidth = std::get<2>(rTerm);
                    bool adjoined = true;
                    uint32_t lsb = 0;
                    if (lLsb + lWidth == rLsb) {
                        lsb = lLsb;
                    } else if (lLsb == rLsb + rWidth) {
                        lsb = rLsb;
                    } else {
                        adjoined = false;
                    }
                    if (adjoined) {
                        APPLYING(REPLACE_ADD_WITH_COUNT_ONES) {
                            DfgSel* const selp
                                = make<DfgSel>(vtxp->fileline(),
                                               DfgDataType::packed(lWidth + rWidth), lVtxp, lsb);
                            DfgVertex* resp
                                = make<DfgCountOnes>(flp, DfgDataType::packed(32), selp);
                            if (vtxp->width() > 32U) {
                                resp = make<DfgConcat>(vtxp, makeZero(flp, vtxp->width() - 32U),
                                                       resp);
                            } else if (vtxp->width() < 32U) {
                                resp = make<DfgSel>(vtxp, resp, 0U);
                            }
                            if (extrap) resp = make<DfgAdd>(vtxp, resp, extrap);
                            replace(resp);
                            return;
                        }
                    }
                }
            }
        }
    }

    void visit(DfgArraySel* const vtxp) override {
        DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>();
        if (!idxp) return;
        DfgVarArray* const varp = vtxp->fromp()->cast<DfgVarArray>();
        if (!varp) return;
        if (varp->varp()->isForced()) return;
        if (varp->varp()->isSigUserRWPublic()) return;
        DfgVertex* const srcp = varp->srcp();
        if (!srcp) return;

        if (DfgSpliceArray* const splicep = srcp->cast<DfgSpliceArray>()) {
            DfgVertex* const driverp = splicep->driverAt(idxp->toSizeT());
            if (!driverp) return;
            DfgUnitArray* const uap = driverp->cast<DfgUnitArray>();
            if (!uap) return;
            if (uap->srcp()->is<DfgVertexSplice>()) return;
            // If driven by a variable that had a Driver in DFG, it is partial
            if (DfgVertexVar* const dvarp = uap->srcp()->cast<DfgVertexVar>()) {
                if (dvarp->srcp()) return;
            }
            APPLYING(INLINE_ARRAYSEL_SPLICE) {
                replace(uap->srcp());
                return;
            }
        }

        if (DfgUnitArray* const uap = srcp->cast<DfgUnitArray>()) {
            UASSERT_OBJ(idxp->toSizeT() == 0, vtxp, "Array index out of range");
            if (uap->srcp()->is<DfgSplicePacked>()) return;
            // If driven by a variable that had a Driver in DFG, it is partial
            if (DfgVertexVar* const dvarp = uap->srcp()->cast<DfgVertexVar>()) {
                if (dvarp->srcp()) return;
            }
            APPLYING(INLINE_ARRAYSEL_UNIT) {
                replace(uap->srcp());
                return;
            }
        }
    }

    void visit(DfgConcat* const vtxp) override {
        if (associativeBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        FileLine* const flp = vtxp->fileline();

        if (isZero(lhsp)) {
            DfgConst* const lConstp = lhsp->as<DfgConst>();
            if (DfgSel* const rSelp = rhsp->cast<DfgSel>()) {
                if (vtxp->dtype() == rSelp->fromp()->dtype() && rSelp->lsb() == lConstp->width()) {
                    APPLYING(REPLACE_CONCAT_ZERO_AND_SEL_TOP_WITH_SHIFTR) {
                        replace(
                            make<DfgShiftR>(vtxp, rSelp->fromp(), makeI32(flp, lConstp->width())));
                        return;
                    }
                }
            }
        }

        if (isZero(rhsp)) {
            DfgConst* const rConstp = rhsp->as<DfgConst>();
            if (DfgSel* const lSelp = lhsp->cast<DfgSel>()) {
                if (vtxp->dtype() == lSelp->fromp()->dtype() && lSelp->lsb() == 0) {
                    APPLYING(REPLACE_CONCAT_SEL_BOTTOM_AND_ZERO_WITH_SHIFTL) {
                        replace(
                            make<DfgShiftL>(vtxp, lSelp->fromp(), makeI32(flp, rConstp->width())));
                        return;
                    }
                }
            }
        }

        if (DfgNot* const lNot = lhsp->cast<DfgNot>()) {
            if (DfgNot* const rNot = rhsp->cast<DfgNot>()) {
                if (!lNot->hasMultipleSinks() && !rNot->hasMultipleSinks()) {
                    APPLYING(PUSH_CONCAT_THROUGH_NOTS) {
                        DfgConcat* const newCatp
                            = make<DfgConcat>(vtxp, lNot->srcp(), rNot->srcp());
                        replace(make<DfgNot>(vtxp, newCatp));
                        return;
                    }
                }
            }
        }

        if (DfgSel* const lSelp = lhsp->cast<DfgSel>()) {
            if (DfgSel* const rSelp = rhsp->cast<DfgSel>()) {
                if (isSame(lSelp->fromp(), rSelp->fromp())) {
                    if (lSelp->lsb() == rSelp->lsb() + rSelp->width()) {
                        APPLYING(REMOVE_CONCAT_OF_ADJOINING_SELS) {
                            replace(make<DfgSel>(vtxp, rSelp->fromp(), rSelp->lsb()));
                            return;
                        }
                    }
                }
            }

            if (DfgConcat* const rConcatp = rhsp->cast<DfgConcat>()) {
                if (DfgSel* const rlSelp = rConcatp->lhsp()->cast<DfgSel>()) {
                    if (isSame(lSelp->fromp(), rlSelp->fromp())) {
                        if (lSelp->lsb() == rlSelp->lsb() + rlSelp->width()) {
                            APPLYING(REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_LHS) {
                                const uint32_t width = lSelp->width() + rlSelp->width();
                                const DfgDataType& dtype = DfgDataType::packed(width);
                                DfgSel* const selp
                                    = make<DfgSel>(flp, dtype, rlSelp->fromp(), rlSelp->lsb());
                                replace(make<DfgConcat>(vtxp, selp, rConcatp->rhsp()));
                                return;
                            }
                        }
                    }
                }
            }
        }

        if (DfgSel* const rSelp = rhsp->cast<DfgSel>()) {
            if (DfgConcat* const lConcatp = lhsp->cast<DfgConcat>()) {
                if (DfgSel* const lrSelp = lConcatp->rhsp()->cast<DfgSel>()) {
                    if (isSame(lrSelp->fromp(), rSelp->fromp())) {
                        if (lrSelp->lsb() == rSelp->lsb() + rSelp->width()) {
                            APPLYING(REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_RHS) {
                                const uint32_t width = lrSelp->width() + rSelp->width();
                                const DfgDataType& dtype = DfgDataType::packed(width);
                                DfgSel* const selp
                                    = make<DfgSel>(flp, dtype, rSelp->fromp(), rSelp->lsb());
                                replace(make<DfgConcat>(vtxp, lConcatp->lhsp(), selp));
                                return;
                            }
                        }
                    }
                }
            }
        }

        if (DfgConst* const lConstp = lhsp->cast<DfgConst>()) {
            if (DfgCond* const rCondp = rhsp->cast<DfgCond>()) {
                DfgVertex* const rtVtxp = rCondp->thenp();
                DfgVertex* const reVtxp = rCondp->elsep();
                DfgConst* const rtConstp = rtVtxp->cast<DfgConst>();
                DfgConst* const reConstp = reVtxp->cast<DfgConst>();
                if (!rCondp->hasMultipleSinks() && (rtConstp || reConstp)) {
                    APPLYING(PUSH_CONCAT_THROUGH_COND_LHS) {
                        DfgVertex* const thenp = [&]() -> DfgVertex* {
                            FileLine* const rtFlp = rtVtxp->fileline();
                            if (rtConstp) {
                                DfgConst* const constp = makeZero(rtFlp, vtxp->width());
                                constp->num().opConcat(lConstp->num(), rtConstp->num());
                                return constp;
                            }
                            return make<DfgConcat>(rtFlp, vtxp->dtype(), lConstp, rtVtxp);
                        }();
                        DfgVertex* const elsep = [&]() -> DfgVertex* {
                            FileLine* const reFlp = reVtxp->fileline();
                            if (reConstp) {
                                DfgConst* const constp = makeZero(reFlp, vtxp->width());
                                constp->num().opConcat(lConstp->num(), reConstp->num());
                                return constp;
                            }
                            return make<DfgConcat>(reFlp, vtxp->dtype(), lConstp, reVtxp);
                        }();
                        replace(make<DfgCond>(vtxp, rCondp->condp(), thenp, elsep));
                        return;
                    }
                }
            }
        }

        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            if (DfgCond* const lCondp = lhsp->cast<DfgCond>()) {
                DfgVertex* const ltVtxp = lCondp->thenp();
                DfgVertex* const leVtxp = lCondp->elsep();
                DfgConst* const ltConstp = ltVtxp->cast<DfgConst>();
                DfgConst* const leConstp = leVtxp->cast<DfgConst>();
                if (!lCondp->hasMultipleSinks() && (ltConstp || leConstp)) {
                    APPLYING(PUSH_CONCAT_THROUGH_COND_RHS) {
                        DfgVertex* const thenp = [&]() -> DfgVertex* {
                            FileLine* const ltFlp = ltVtxp->fileline();
                            if (ltConstp) {
                                DfgConst* const constp = makeZero(ltFlp, vtxp->width());
                                constp->num().opConcat(ltConstp->num(), rConstp->num());
                                return constp;
                            }
                            return make<DfgConcat>(ltFlp, vtxp->dtype(), ltVtxp, rConstp);
                        }();
                        DfgVertex* const elsep = [&]() -> DfgVertex* {
                            FileLine* const leFlp = leVtxp->fileline();
                            if (leConstp) {
                                DfgConst* const constp = makeZero(leFlp, vtxp->width());
                                constp->num().opConcat(leConstp->num(), rConstp->num());
                                return constp;
                            }
                            return make<DfgConcat>(leFlp, vtxp->dtype(), leVtxp, rConstp);
                        }();

                        replace(make<DfgCond>(vtxp, lCondp->condp(), thenp, elsep));
                        return;
                    }
                }
            }
        }

        // Attempt to narrow a concatenation that produces unused bits on the edges
        {
            const uint32_t vMsb = vtxp->width() - 1;  // MSB of the concatenation
            const uint32_t lLsb = vtxp->rhsp()->width();  // LSB of the LHS
            const uint32_t rMsb = lLsb - 1;  // MSB of the RHS
            // Check each sink, and record the range of bits used by them
            uint32_t lsb = vMsb;  // LSB used by a sink
            uint32_t msb = 0;  // MSB used by a sink
            bool hasCrossSink = false;  // True if some sinks use bits from both sides
            vtxp->foreachSink([&](DfgVertex& sink) {
                // Record bits used by DfgSel sinks
                if (const DfgSel* const selp = sink.cast<DfgSel>()) {
                    const uint32_t selLsb = selp->lsb();
                    const uint32_t selMsb = selLsb + selp->width() - 1;
                    lsb = std::min(lsb, selLsb);
                    msb = std::max(msb, selMsb);
                    hasCrossSink |= selMsb >= lLsb && rMsb >= selLsb;
                    return false;
                }
                // Ignore non-observable variable sinks. These will be eliminated.
                if (const DfgVarPacked* const varp = sink.cast<DfgVarPacked>()) {
                    if (!varp->hasSinks() && !varp->isObserved()) return false;
                }
                // Otherwise the whole value is used
                lsb = 0;
                msb = vMsb;
                return true;
            });
            if (hasCrossSink && (vMsb > msb || lsb > 0)) {
                APPLYING(NARROW_CONCAT) {
                    // Narrowed RHS
                    DfgVertex* nRhsp = rhsp;
                    if (lsb != 0)
                        nRhsp = make<DfgSel>(flp, DfgDataType::packed(rMsb - lsb + 1), rhsp, lsb);
                    // Narrowed LHS
                    DfgVertex* nLhsp = lhsp;
                    if (msb != vMsb)
                        nLhsp = make<DfgSel>(flp, DfgDataType::packed(msb - lLsb + 1), lhsp, 0U);
                    // Narrowed concatenation
                    DfgVertex* const catp
                        = make<DfgConcat>(flp, DfgDataType::packed(msb - lsb + 1), nLhsp, nRhsp);

                    // Need to insert via a partial splice to avoid infinite matching,
                    // this splice will be eliminated on later visits to its sinks.
                    const DfgVertex::ScopeCache scopeCache;
                    DfgSplicePacked* const sp = new DfgSplicePacked{m_dfg, flp, vtxp->dtype()};
                    sp->addDriver(catp, lsb, flp);
                    m_vInfo[sp].m_id = ++m_lastId;
                    replace(sp);
                    return;
                }
            }
        }
    }

    void visit(DfgDiv* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgDivS* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgEq* const vtxp) override {
        if (foldBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_EQ) {
                replace(makeOnes(flp, 1));
                return;
            }
        }

        if (DfgConst* const lhsConstp = lhsp->cast<DfgConst>()) {
            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushCompareOpThroughConcat(vtxp, lhsConstp, rhsConcatp)) return;
            }
        }
    }

    void visit(DfgGt* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_GT) {
                replace(makeZero(flp, 1));
                return;
            }
        }
    }

    void visit(DfgGtS* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_GTS) {
                replace(makeZero(flp, 1));
                return;
            }
        }
    }

    void visit(DfgGte* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_GTE) {
                replace(makeOnes(flp, 1));
                return;
            }
        }
    }

    void visit(DfgGteS* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_GTES) {
                replace(makeOnes(flp, 1));
                return;
            }
        }
    }

    void visit(DfgLogAnd* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (lhsp->width() == 1 && rhsp->width() == 1) {
            APPLYING(REPLACE_LOGAND_WITH_AND) {
                replace(make<DfgAnd>(vtxp, lhsp, rhsp));
                return;
            }
        }
    }

    void visit(DfgLogEq* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgLogIf* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgLogOr* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (lhsp->width() == 1 && rhsp->width() == 1) {
            APPLYING(REPLACE_LOGOR_WITH_OR) {
                replace(make<DfgOr>(vtxp, lhsp, rhsp));
                return;
            }
        }
    }

    void visit(DfgLt* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_LT) {
                replace(makeZero(flp, 1));
                return;
            }
        }
    }

    void visit(DfgLtS* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_LTS) {
                replace(makeZero(flp, 1));
                return;
            }
        }
    }

    void visit(DfgLte* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_LTE) {
                replace(makeOnes(flp, 1));
                return;
            }
        }
    }

    void visit(DfgLteS* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_LTES) {
                replace(makeOnes(flp, 1));
                return;
            }
        }
    }

    void visit(DfgModDiv* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgModDivS* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgMul* const vtxp) override {
        if (associativeBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;
    }

    void visit(DfgMulS* const vtxp) override {
        if (associativeBinary(vtxp)) return;

        if (commutativeBinary(vtxp)) return;
    }

    void visit(DfgNeq* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (isSame(lhsp, rhsp)) {
            APPLYING(FOLD_SELF_NEQ) {
                replace(makeZero(flp, 1));
                return;
            }
        }
    }

    void visit(DfgPow* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgPowSS* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgPowSU* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgPowUS* const vtxp) override {
        if (foldBinary(vtxp)) return;
    }

    void visit(DfgReplicate* const vtxp) override {
        if (vtxp->dtype() == vtxp->srcp()->dtype()) {
            APPLYING(REMOVE_REPLICATE_ONCE) {
                replace(vtxp->srcp());
                return;
            }
        }

        if (foldBinary(vtxp)) return;
    }

    void visit(DfgShiftL* const vtxp) override {
        if (foldBinary(vtxp)) return;
        if (optimizeShiftRHS(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (DfgShiftL* const lShiftLp = lhsp->cast<DfgShiftL>()) {
            if (!lShiftLp->hasMultipleSinks() && rhsp->dtype() == lShiftLp->rhsp()->dtype()) {
                APPLYING(REPLACE_SHIFTL_SHIFTL) {
                    DfgAdd* const addp = make<DfgAdd>(rhsp, rhsp, lShiftLp->rhsp());
                    replace(make<DfgShiftL>(vtxp, lShiftLp->lhsp(), addp));
                    return;
                }
            }
        }

        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();

            if (shiftAmount == 0) {
                APPLYING(REMOVE_SHIFTL_ZERO) {
                    replace(lhsp);
                    return;
                }
            }

            if (shiftAmount >= vtxp->width()) {
                APPLYING(REPLACE_SHIFTL_OVER) {
                    replace(makeZero(vtxp->fileline(), vtxp->width()));
                    return;
                }
            }

            if (DfgConcat* const lConcatp = lhsp->cast<DfgConcat>()) {
                if (!lConcatp->hasMultipleSinks()) {
                    APPLYING(REPLACE_SHIFTL_CAT) {
                        DfgVertex* const lRhsp = lConcatp->rhsp();
                        DfgVertex* const lLhsp = lConcatp->lhsp();
                        // Compute widths of 3 possible result parts
                        const uint32_t rW = shiftAmount;
                        const uint32_t mW = std::min(lRhsp->width(), vtxp->width() - shiftAmount);
                        const uint32_t lW = vtxp->width() - mW - rW;
                        // Construct the result
                        FileLine* const flp = lConcatp->fileline();
                        DfgVertex* const rp = makeZero(flp, shiftAmount);
                        DfgVertex* const mp
                            = make<DfgSel>(flp, DfgDataType::packed(mW), lRhsp, 0U);
                        DfgVertex* np = make<DfgConcat>(flp, DfgDataType::packed(mW + rW), mp, rp);
                        if (!lW) {
                            replace(np);
                            return;
                        }
                        DfgVertex* const lp
                            = make<DfgSel>(flp, DfgDataType::packed(lW), lLhsp, 0U);
                        np = make<DfgConcat>(vtxp, lp, np);
                        replace(np);
                        return;
                    }
                }
            }

            if (DfgSel* const lSelp = lhsp->cast<DfgSel>()) {
                if (!lSelp->hasMultipleSinks()) {
                    APPLYING(REPLACE_SHIFTL_SEL) {
                        const uint32_t nSelWidth = lSelp->width() - shiftAmount;
                        DfgVertex* const nSelp
                            = make<DfgSel>(lSelp->fileline(), DfgDataType::packed(nSelWidth),
                                           lSelp->fromp(), lSelp->lsb());
                        replace(
                            make<DfgConcat>(vtxp, nSelp, makeZero(vtxp->fileline(), shiftAmount)));
                        return;
                    }
                }
            }

            if (DfgCond* const lCondp = lhsp->cast<DfgCond>()) {
                if (!lCondp->hasMultipleSinks()) {
                    APPLYING(PUSH_SHIFTL_THROUGH_COND) {
                        DfgShiftL* const tp = make<DfgShiftL>(vtxp, lCondp->thenp(), rConstp);
                        DfgShiftL* const ep = make<DfgShiftL>(vtxp, lCondp->elsep(), rConstp);
                        replace(make<DfgCond>(vtxp, lCondp->condp(), tp, ep));
                        return;
                    }
                }
            }
        }
    }

    void visit(DfgShiftR* const vtxp) override {
        if (foldBinary(vtxp)) return;
        if (optimizeShiftRHS(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (DfgShiftR* const lShiftRp = lhsp->cast<DfgShiftR>()) {
            if (!lShiftRp->hasMultipleSinks() && rhsp->dtype() == lShiftRp->rhsp()->dtype()) {
                APPLYING(REPLACE_SHIFTR_SHIFTR) {
                    DfgAdd* const addp = make<DfgAdd>(rhsp, rhsp, lShiftRp->rhsp());
                    replace(make<DfgShiftR>(vtxp, lShiftRp->lhsp(), addp));
                    return;
                }
            }
        }

        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            const uint32_t shiftAmount = rConstp->toU32();

            if (shiftAmount == 0) {
                APPLYING(REMOVE_SHIFTR_ZERO) {
                    replace(lhsp);
                    return;
                }
            }

            if (shiftAmount >= vtxp->width()) {
                APPLYING(REPLACE_SHIFTR_OVER) {
                    replace(makeZero(vtxp->fileline(), vtxp->width()));
                    return;
                }
            }

            if (DfgConcat* const lConcatp = lhsp->cast<DfgConcat>()) {
                if (!lConcatp->hasMultipleSinks()) {
                    APPLYING(REPLACE_SHIFTR_CAT) {
                        DfgVertex* const lRhsp = lConcatp->rhsp();
                        DfgVertex* const lLhsp = lConcatp->lhsp();
                        // Compute widths of 3 possible result parts
                        const uint32_t lW = shiftAmount;
                        const uint32_t mW = std::min(lLhsp->width(), vtxp->width() - shiftAmount);
                        const uint32_t rW = vtxp->width() - mW - lW;
                        // Construct the result
                        FileLine* const flp = lConcatp->fileline();
                        DfgVertex* const lp = makeZero(flp, shiftAmount);
                        DfgVertex* const mp = make<DfgSel>(flp, DfgDataType::packed(mW), lLhsp,
                                                           lLhsp->width() - mW);
                        DfgVertex* np = make<DfgConcat>(flp, DfgDataType::packed(lW + mW), lp, mp);
                        if (!rW) {
                            replace(np);
                            return;
                        }
                        DfgVertex* const rp = make<DfgSel>(flp, DfgDataType::packed(rW), lRhsp,
                                                           lRhsp->width() - rW);
                        np = make<DfgConcat>(vtxp, np, rp);
                        replace(np);
                        return;
                    }
                }
            }

            if (DfgSel* const lSelp = lhsp->cast<DfgSel>()) {
                if (!lSelp->hasMultipleSinks()) {
                    APPLYING(REPLACE_SHIFTR_SEL) {
                        const uint32_t nSelWidth = lSelp->width() - shiftAmount;
                        DfgVertex* const nSelp
                            = make<DfgSel>(lSelp->fileline(), DfgDataType::packed(nSelWidth),
                                           lSelp->fromp(), lSelp->lsb() + shiftAmount);
                        replace(
                            make<DfgConcat>(vtxp, makeZero(vtxp->fileline(), shiftAmount), nSelp));
                        return;
                    }
                }
            }

            if (DfgCond* const lCondp = lhsp->cast<DfgCond>()) {
                if (!lCondp->hasMultipleSinks()) {
                    APPLYING(PUSH_SHIFTR_THROUGH_COND) {
                        DfgShiftR* const tp = make<DfgShiftR>(vtxp, lCondp->thenp(), rConstp);
                        DfgShiftR* const ep = make<DfgShiftR>(vtxp, lCondp->elsep(), rConstp);
                        replace(make<DfgCond>(vtxp, lCondp->condp(), tp, ep));
                        return;
                    }
                }
            }
        }
    }

    void visit(DfgShiftRS* const vtxp) override {
        if (foldBinary(vtxp)) return;
        if (optimizeShiftRHS(vtxp)) return;
    }

    void visit(DfgSub* const vtxp) override {
        if (foldBinary(vtxp)) return;

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            if (rConstp->isZero()) {
                APPLYING(REMOVE_SUB_ZERO) {
                    replace(lhsp);
                    return;
                }
            }
            if (vtxp->dtype() == m_bitDType && rConstp->hasValue(1)) {
                APPLYING(REPLACE_SUB_WITH_NOT) {
                    replace(make<DfgNot>(vtxp->fileline(), m_bitDType, lhsp));
                    return;
                }
            }
        }
    }

    //=========================================================================
    //  DfgVertexTernary
    //=========================================================================

    void visit(DfgCond* const vtxp) override {
        DfgVertex* const condp = vtxp->condp();
        DfgVertex* const thenp = vtxp->thenp();
        DfgVertex* const elsep = vtxp->elsep();
        FileLine* const flp = vtxp->fileline();

        if (condp->dtype() != m_bitDType) return;

        if (isOnes(condp)) {
            APPLYING(REMOVE_COND_WITH_TRUE_CONDITION) {
                replace(thenp);
                return;
            }
        }

        if (isZero(condp)) {
            APPLYING(REMOVE_COND_WITH_FALSE_CONDITION) {
                replace(elsep);
                return;
            }
        }

        if (isSame(thenp, elsep)) {
            APPLYING(REMOVE_COND_WITH_BRANCHES_SAME) {
                replace(elsep);
                return;
            }
        }

        if (DfgNot* const condNotp = condp->cast<DfgNot>()) {
            if (!condp->hasMultipleSinks() || condNotp->hasMultipleSinks()) {
                APPLYING(SWAP_COND_WITH_NOT_CONDITION) {
                    replace(make<DfgCond>(vtxp, condNotp->srcp(), elsep, thenp));
                    return;
                }
            }
        }

        if (DfgNeq* const condNeqp = condp->cast<DfgNeq>()) {
            if (!condp->hasMultipleSinks()) {
                APPLYING(SWAP_COND_WITH_NEQ_CONDITION) {
                    DfgEq* const newCondp = make<DfgEq>(condp, condNeqp->lhsp(), condNeqp->rhsp());
                    replace(make<DfgCond>(vtxp, newCondp, elsep, thenp));
                    return;
                }
            }
        }

        if (DfgNot* const thenNotp = thenp->cast<DfgNot>()) {
            if (DfgNot* const elseNotp = elsep->cast<DfgNot>()) {
                if (!thenNotp->srcp()->is<DfgConst>() && !elseNotp->srcp()->is<DfgConst>()
                    && !thenNotp->hasMultipleSinks() && !elseNotp->hasMultipleSinks()) {
                    APPLYING(PULL_NOTS_THROUGH_COND) {
                        DfgCond* const newCondp = make<DfgCond>(
                            vtxp, vtxp->condp(), thenNotp->srcp(), elseNotp->srcp());
                        replace(make<DfgNot>(thenp->fileline(), vtxp->dtype(), newCondp));
                        return;
                    }
                }
            }
        }

        if (DfgOr* const condOrp = condp->cast<DfgOr>()) {
            if (DfgCond* const thenCondp = thenp->cast<DfgCond>()) {
                if (!thenCondp->hasMultipleSinks()) {
                    if (condOrp->lhsp() == thenCondp->condp()) {
                        // '(a | b) ? (a ? x : y) : z' -> 'a ? x : b ? y : z'
                        APPLYING(REPLACE_COND_OR_THEN_COND_LHS) {
                            DfgCond* const ep = make<DfgCond>(thenCondp, condOrp->rhsp(),
                                                              thenCondp->elsep(), elsep);
                            replace(make<DfgCond>(vtxp, condOrp->lhsp(), thenCondp->thenp(), ep));
                            return;
                        }
                    }
                    if (condOrp->rhsp() == thenCondp->condp()) {
                        // '(a | b) ? (a ? x : y) : z' -> 'a ? x : b ? y : z'
                        APPLYING(REPLACE_COND_OR_THEN_COND_RHS) {
                            DfgCond* const ep = make<DfgCond>(thenCondp, condOrp->lhsp(),
                                                              thenCondp->elsep(), elsep);
                            replace(make<DfgCond>(vtxp, condOrp->rhsp(), thenCondp->thenp(), ep));
                            return;
                        }
                    }
                }
            }
        }

        if (vtxp->width() > 1) {
            // 'cond ? a + 1 : a' -> 'a + cond'
            if (DfgAdd* const thenAddp = thenp->cast<DfgAdd>()) {
                if (DfgConst* const constp = thenAddp->lhsp()->cast<DfgConst>()) {
                    if (constp->hasValue(1)) {
                        if (thenAddp->rhsp() == elsep) {
                            APPLYING(REPLACE_COND_INC) {
                                DfgConcat* const extp = make<DfgConcat>(
                                    vtxp, makeZero(flp, vtxp->width() - 1), condp);
                                FileLine* const thenFlp = thenAddp->fileline();
                                replace(
                                    make<DfgAdd>(thenFlp, vtxp->dtype(), thenAddp->rhsp(), extp));
                                return;
                            }
                        }
                    }
                }
            }
            // 'cond ? a - 1 : a' -> 'a - cond'
            if (DfgSub* const thenSubp = thenp->cast<DfgSub>()) {
                if (DfgConst* const constp = thenSubp->rhsp()->cast<DfgConst>()) {
                    if (constp->hasValue(1)) {
                        if (thenSubp->lhsp() == elsep) {
                            APPLYING(REPLACE_COND_DEC) {
                                DfgConcat* const extp = make<DfgConcat>(
                                    vtxp, makeZero(flp, vtxp->width() - 1), condp);
                                FileLine* const thenFlp = thenSubp->fileline();
                                replace(
                                    make<DfgSub>(thenFlp, vtxp->dtype(), thenSubp->lhsp(), extp));
                                return;
                            }
                        }
                    }
                }
            }
        }

        if (vtxp->dtype() == m_bitDType) {
            if (isZero(thenp)) {  // a ? 0 : b becomes ~a & b
                APPLYING(REPLACE_COND_WITH_THEN_BRANCH_ZERO) {
                    replace(make<DfgAnd>(vtxp, make<DfgNot>(vtxp, condp), elsep));
                    return;
                }
            }
            if (thenp == condp) {  // a ? a : b becomes a | b
                APPLYING(REPLACE_COND_WITH_THEN_BRANCH_COND) {
                    replace(make<DfgOr>(vtxp, condp, elsep));
                    return;
                }
            }
            if (elsep == condp) {  // a ? b : a becomes a & b
                APPLYING(REPLACE_COND_WITH_ELSE_BRANCH_COND) {
                    replace(make<DfgAnd>(vtxp, condp, thenp));
                    return;
                }
            }
            if (isOnes(thenp)) {  // a ? 1 : b becomes a | b
                APPLYING(REPLACE_COND_WITH_THEN_BRANCH_ONES) {
                    replace(make<DfgOr>(vtxp, condp, elsep));
                    return;
                }
            }
            if (isZero(elsep)) {  // a ? b : 0 becomes a & b
                APPLYING(REPLACE_COND_WITH_ELSE_BRANCH_ZERO) {
                    replace(make<DfgAnd>(vtxp, condp, thenp));
                    return;
                }
            }
            if (isOnes(elsep)) {  // a ? b : 1 becomes ~a | b
                APPLYING(REPLACE_COND_WITH_ELSE_BRANCH_ONES) {
                    replace(make<DfgOr>(vtxp, make<DfgNot>(vtxp, condp), thenp));
                    return;
                }
            }
        }

        if (DfgConcat* const tConcatp = thenp->cast<DfgConcat>()) {
            if (DfgConcat* const eConcatp = elsep->cast<DfgConcat>()) {
                DfgVertex* const tRhsp = tConcatp->rhsp();
                DfgVertex* const tLhsp = tConcatp->lhsp();
                DfgVertex* const eRhsp = eConcatp->rhsp();
                DfgVertex* const eLhsp = eConcatp->lhsp();

                if (isSame(tRhsp, eRhsp)) {
                    APPLYING(REPLACE_COND_SAME_CAT_RHS) {
                        DfgCond* const newCondp
                            = make<DfgCond>(flp, tLhsp->dtype(), condp, tLhsp, eLhsp);
                        replace(make<DfgConcat>(vtxp, newCondp, tRhsp));
                        return;
                    }
                }

                if (isSame(tLhsp, eLhsp)) {
                    APPLYING(REPLACE_COND_SAME_CAT_LHS) {
                        DfgCond* const newCondp
                            = make<DfgCond>(flp, tRhsp->dtype(), condp, tRhsp, eRhsp);
                        replace(make<DfgConcat>(vtxp, tLhsp, newCondp));
                        return;
                    }
                }
            }
        }

        if (isZero(elsep) && isEqOne(thenp)) {
            APPLYING(REPLACE_COND_CONST_ONE_ZERO) {
                DfgVertex* resp = condp;
                if (const uint32_t extend = vtxp->width() - 1) {
                    DfgConst* const zerop = makeZero(flp, extend);
                    resp = make<DfgConcat>(vtxp, zerop, resp);
                }
                replace(resp);
                return;
            }
        }

        if (isZero(thenp) && isEqOne(elsep)) {
            APPLYING(REPLACE_COND_CONST_ZERO_ONE) {
                DfgVertex* resp = make<DfgNot>(condp, condp);
                if (const uint32_t extend = vtxp->width() - 1) {
                    DfgConst* const zerop = makeZero(vtxp->fileline(), extend);
                    resp = make<DfgConcat>(vtxp, zerop, resp);
                }
                replace(resp);
                return;
            }
        }

        if (DfgCond* const tCondp = thenp->cast<DfgCond>()) {
            if (isSame(condp, tCondp->condp())) {
                APPLYING(REPLACE_COND_SAME_COND_THEN) {
                    replace(make<DfgCond>(vtxp, condp, tCondp->thenp(), elsep));
                    return;
                }
            }
        }

        if (DfgCond* const eCondp = elsep->cast<DfgCond>()) {
            if (isSame(condp, eCondp->condp())) {
                APPLYING(REPLACE_COND_SAME_COND_ELSE) {
                    replace(make<DfgCond>(vtxp, condp, thenp, eCondp->elsep()));
                    return;
                }
            }
        }
    }

    void visit(DfgVertexVar* const vtxp) override {
        if (vtxp->hasSinks()) return;
        if (vtxp->isObserved()) return;
        if (vtxp->defaultp()) return;

        // If undriven, or driven from another var, it is completely redundant.
        if (!vtxp->srcp() || vtxp->srcp()->is<DfgVertexVar>()) {
            APPLYING(REMOVE_VAR) {
                deleteVertex(vtxp);
                return;
            }
        }

        // Otherwise remove if there is only one sink that is not a removable variable
        bool foundOne = false;
        const bool keep = vtxp->srcp()->foreachSink([&](DfgVertex& sink) -> bool {
            // Ignore non-observable variable sinks. These can be eliminated.
            if (const DfgVertexVar* const varp = sink.cast<DfgVertexVar>()) {
                if (!varp->hasSinks() && !varp->isObserved()) return false;
            }
            // Keep before final scoped run if feeds an Ast reference
            if (sink.is<DfgVertexAst>() && m_dfg.modulep()) return true;
            // Keep if found more than one sink
            if (foundOne) return true;
            // Mark first sink found
            foundOne = true;
            return false;
        });
        if (!keep) {
            APPLYING(REMOVE_VAR) {
                deleteVertex(vtxp);
                return;
            }
        }
    }

    V3DfgPeephole(DfgGraph& dfg, V3DfgPeepholeContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {

        // Assign vertex IDs
        m_dfg.forEachVertex([&](DfgVertex& vtx) { m_vInfo[vtx].m_id = ++m_lastId; });

        // Initialize the work list and iter list. They can't get bigger than
        // m_dfg.size(), but new vertices are created in the loop, so over alloacte
        m_workList.reserve(m_dfg.size() * 2);
        m_iterList.reserve(m_dfg.size() * 2);

        // Need a nullptr at index 0 so VertexInfo::m_*ListIndex == 0 can check membership
        m_workList.push_back(nullptr);
        m_iterList.push_back(nullptr);

        // Add all variable vertices to the work list. Do this first so they are processed
        // last. This order has a better chance of preserving original variables in case
        // they are needed to hold intermediate results.
        for (DfgVertexVar& vtx : m_dfg.varVertices()) addToWorkList(&vtx);

        // Add all operation vertices to the work list
        for (DfgVertex& vtx : m_dfg.opVertices()) addToWorkList(&vtx);

        // Process iteratively
        while (true) {
            // Process the work list - keep the placeholder at index 0
            while (m_workList.size() > 1) {
                VL_RESTORER(m_vtxp);

                // Pop up head of work list
                m_vtxp = m_workList.back();
                m_workList.pop_back();
                if (!m_vtxp) continue;  // If removed from worklist (deleted), move on
                m_vInfo[m_vtxp].m_workListIndex = 0;  // No longer on work list

                // Variables are special, just visit them, the visit might delete them
                if (DfgVertexVar* const varp = m_vtxp->cast<DfgVertexVar>()) {
                    visit(varp);
                    continue;
                }

                // Ast references are not considered
                if (m_vtxp->is<DfgVertexAst>()) continue;

                // Unsued vertices should have been removed immediately
                UASSERT_OBJ(m_vtxp->hasSinks(), m_vtxp, "Operation vertex should have sinks");

                // Check if an equivalent vertex exists, if so replace this vertex with it
                if (DfgVertex* const sampep = m_cache.cache(m_vtxp)) {
                    APPLYING(REPLACE_WITH_EQUIVALENT) {
                        replace(sampep);
                        continue;
                    }
                }

                // Visit vertex, might get deleted in the process
                iterate(m_vtxp);
            }

            // If nothing was added to the iter list, we can stop
            if (m_iterList.size() == 1) break;

            // Expand the iter list to visit the whole neighborhood of vertices
            // within a fixed number of hops from the enqueued vertices. This
            // enables patterns that look deeper across the graph to be reconsidered.
            {
                size_t begin = 0;
                size_t end = m_iterList.size();
                for (size_t hops = 1; hops <= 4; ++hops) {
                    for (size_t i = begin; i < end; ++i) {
                        DfgVertex* const vtxp = m_iterList[i];
                        if (!vtxp) continue;
                        vtxp->foreachSink([&](DfgVertex& dst) {
                            addToIterList(&dst);
                            return false;
                        });
                        vtxp->foreachSource([&](DfgVertex& src) {
                            addToIterList(&src);
                            return false;
                        });
                    }
                    begin = end;
                    end = m_iterList.size();
                }
            }

            // Move vertices in the iter list to the work list for the next iteration
            for (DfgVertex* const vtxp : m_iterList) {
                if (!vtxp) continue;
                removeFromIterList(vtxp);
                addToWorkList(vtxp);
            }
            // Reset the iter list
            m_iterList.resize(1);
        }
    }

#undef APPLYING

public:
    static void apply(DfgGraph& dfg, V3DfgPeepholeContext& ctx) { V3DfgPeephole{dfg, ctx}; }
};

V3DebugBisect V3DfgPeephole::s_debugBisect{"DfgPeephole"};

void V3DfgPasses::peephole(DfgGraph& dfg, V3DfgPeepholeContext& ctx) {
    if (!v3Global.opt.fDfgPeephole()) return;
    V3DfgPeephole::apply(dfg, ctx);
}
