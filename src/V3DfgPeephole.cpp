// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Peephole optimizations over DfgGraph
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
//
// A pattern-matching based optimizer for DfgGraph. This is in some aspects similar to V3Const, but
// more powerful in that it does not care about ordering combinational statement. This is also less
// broadly applicable than V3Const, as it does not apply to procedural statements with sequential
// execution semantics.
//
//*************************************************************************

#include "config_build.h"

#include "V3DfgPeephole.h"

#include "V3Ast.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Stats.h"

#include <algorithm>
#include <cctype>

VL_DEFINE_DEBUG_FUNCTIONS;

V3DfgPeepholeContext::V3DfgPeepholeContext(const std::string& label)
    : m_label{label} {
    const auto checkEnabled = [this](VDfgPeepholePattern id) {
        string str{id.ascii()};
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
    const auto emitStat = [this](VDfgPeepholePattern id) {
        string str{id.ascii()};
        std::transform(str.begin(), str.end(), str.begin(), [](unsigned char c) {  //
            return c == '_' ? ' ' : std::tolower(c);
        });
        V3Stats::addStat("Optimizations, DFG " + m_label + " Peephole, " + str, m_count[id]);
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
template <typename T_Reductoin>
using ReductionToBitwise = typename ReductionToBitwiseImpl<T_Reductoin>::type;

template <typename T_Bitwise>
struct BitwiseToReductionImpl {};
template <> struct BitwiseToReductionImpl<DfgAnd> { using type = DfgRedAnd; };
template <> struct BitwiseToReductionImpl<DfgOr>  { using type = DfgRedOr;  };
template <> struct BitwiseToReductionImpl<DfgXor> { using type = DfgRedXor; };
template <typename T_Reductoin>
using BitwiseToReduction = typename BitwiseToReductionImpl<T_Reductoin>::type;
// clang-format on

class V3DfgPeephole final : public DfgVisitor {

    // STATE
    DfgGraph& m_dfg;  // The DfgGraph being visited
    V3DfgPeepholeContext& m_ctx;  // The config structure
    bool m_changed = false;  // Changed a vertex
    AstNodeDType* const m_bitDType = DfgVertex::dtypeForWidth(1);  // Common, so grab it up front

#define APPLYING(id) if (checkApplying(VDfgPeepholePattern::id))

    // METHODS
    bool checkApplying(VDfgPeepholePattern id) {
        if (!m_ctx.m_enabled[id]) return false;
        UINFO(9, "Applying DFG patten " << id.ascii() << endl);
        ++m_ctx.m_count[id];
        m_changed = true;
        return true;
    }

    // Shorthand
    static AstNodeDType* dtypeForWidth(uint32_t width) { return DfgVertex::dtypeForWidth(width); }

    // Create a new DfgConst vertex with the given width and value
    DfgConst* makeConst(FileLine* flp, uint32_t width, uint32_t value) {
        const int widthInt = static_cast<int>(width);
        return new DfgConst{m_dfg, new AstConst{flp, AstConst::WidthedValue{}, widthInt, value}};
    }

    // Create a new 32-bit DfgConst vertex
    DfgConst* makeI32(FileLine* flp, uint32_t value) { return makeConst(flp, 32, value); }

    // Create a new DfgConst vertex with the given width and value zero
    DfgConst* makeZero(FileLine* flp, uint32_t width) { return makeConst(flp, width, 0); }

    // Transformations that apply to all commutative binary vertices
    void commutativeBinary(DfgVertexWithArity<2>* vtxp) {
        DfgVertex* const lhsp = vtxp->source<0>();
        DfgVertex* const rhsp = vtxp->source<1>();
        // Ensure Const is on left-hand side to simplify other patterns
        if (lhsp->is<DfgConst>()) return;
        if (rhsp->is<DfgConst>()) {
            APPLYING(SWAP_CONST_IN_COMMUTATIVE_BINARY) {
                vtxp->lhsp(rhsp);
                vtxp->rhsp(lhsp);
                return;
            }
        }
        // Ensure Not is on the left-hand side to simplify other patterns
        if (lhsp->is<DfgNot>()) return;
        if (rhsp->is<DfgNot>()) {
            APPLYING(SWAP_NOT_IN_COMMUTATIVE_BINARY) {
                vtxp->lhsp(rhsp);
                vtxp->rhsp(lhsp);
                return;
            }
        }
        // If both sides are variable references, order the side in some defined way. This allows
        // CSE to later merge 'a op b' with 'b op a'.
        if (lhsp->is<DfgVarPacked>() && rhsp->is<DfgVarPacked>()) {
            AstVar* const lVarp = lhsp->as<DfgVarPacked>()->varp();
            AstVar* const rVarp = rhsp->as<DfgVarPacked>()->varp();
            if (lVarp->name() > rVarp->name()) {
                APPLYING(SWAP_VAR_IN_COMMUTATIVE_BINARY) {
                    vtxp->lhsp(rhsp);
                    vtxp->rhsp(lhsp);
                    return;
                }
            }
        }
    }

    // Transformations that apply to all associative binary vertices
    void associativeBinary(DfgVertexWithArity<2>* vtxp) {
        DfgVertex* const lhsp = vtxp->lhsp();

        // Make associative trees right leaning (for better CSE opportunities)
        if (lhsp->type() == vtxp->type() && !lhsp->hasMultipleSinks()) {
            DfgVertexWithArity<2>* const lBinp = static_cast<DfgVertexWithArity<2>*>(lhsp);
            APPLYING(RIGHT_LEANING_ASSOC) {
                vtxp->replaceWith(lBinp);
                vtxp->lhsp(lBinp->rhsp());
                lBinp->rhsp(vtxp);
                return;
            }
        }
    }

    // Bitwise operation with one side Const, and the other side a Concat
    template <typename Vertex>
    bool tryPushBitwiseOpThroughConcat(Vertex* vtxp, DfgConst* constp, DfgConcat* concatp) {
        UASSERT_OBJ(constp->width() == concatp->width(), vtxp, "Mismatched widths");

        FileLine* const flp = vtxp->fileline();

        // If at least one of the sides of the Concat constant, or width 1 (i.e.: can be
        // further simplified), then push the Vertex past the Concat
        if (concatp->lhsp()->is<DfgConst>() || concatp->rhsp()->is<DfgConst>()  //
            || concatp->lhsp()->width() == 1 || concatp->rhsp()->width() == 1) {
            APPLYING(PUSH_BITWISE_OP_THROUGH_CONCAT) {
                const uint32_t width = concatp->width();
                AstNodeDType* const lDtypep = concatp->lhsp()->dtypep();
                AstNodeDType* const rDtypep = concatp->rhsp()->dtypep();
                const uint32_t lWidth = lDtypep->width();
                const uint32_t rWidth = rDtypep->width();

                // The new Lhs vertex
                Vertex* const newLhsp = new Vertex{m_dfg, flp, lDtypep};
                DfgConst* const newLhsConstp = makeZero(constp->fileline(), lWidth);
                newLhsConstp->num().opSel(constp->num(), width - 1, rWidth);
                newLhsp->lhsp(newLhsConstp);
                newLhsp->rhsp(concatp->lhsp());

                // The new Rhs vertex
                Vertex* const newRhsp = new Vertex{m_dfg, flp, rDtypep};
                DfgConst* const newRhsConstp = makeZero(constp->fileline(), rWidth);
                newRhsConstp->num().opSel(constp->num(), rWidth - 1, 0);
                newRhsp->lhsp(newRhsConstp);
                newRhsp->rhsp(concatp->rhsp());

                // The replacement Concat vertex
                DfgConcat* const newConcat
                    = new DfgConcat{m_dfg, concatp->fileline(), concatp->dtypep()};
                newConcat->lhsp(newLhsp);
                newConcat->rhsp(newRhsp);

                // Replace this vertex
                vtxp->replaceWith(newConcat);
                return true;
            }
        }
        return false;
    }

    template <typename Vertex>
    bool tryPushCompareOpThroughConcat(Vertex* vtxp, DfgConst* constp, DfgConcat* concatp) {
        UASSERT_OBJ(constp->width() == concatp->width(), vtxp, "Mismatched widths");

        FileLine* const flp = vtxp->fileline();

        // If at least one of the sides of the Concat is constant, then push the Vertex past the
        // Concat
        if (concatp->lhsp()->is<DfgConst>() || concatp->rhsp()->is<DfgConst>()) {
            APPLYING(PUSH_COMPARE_OP_THROUGH_CONCAT) {
                const uint32_t width = concatp->width();
                const uint32_t lWidth = concatp->lhsp()->width();
                const uint32_t rWidth = concatp->rhsp()->width();

                // The new Lhs vertex
                Vertex* const newLhsp = new Vertex{m_dfg, flp, m_bitDType};
                DfgConst* const newLhsConstp = makeZero(constp->fileline(), lWidth);
                newLhsConstp->num().opSel(constp->num(), width - 1, rWidth);
                newLhsp->lhsp(newLhsConstp);
                newLhsp->rhsp(concatp->lhsp());

                // The new Rhs vertex
                Vertex* const newRhsp = new Vertex{m_dfg, flp, m_bitDType};
                DfgConst* const newRhsConstp = makeZero(constp->fileline(), rWidth);
                newRhsConstp->num().opSel(constp->num(), rWidth - 1, 0);
                newRhsp->lhsp(newRhsConstp);
                newRhsp->rhsp(concatp->rhsp());

                // The replacement Vertex
                DfgVertexWithArity<2>* const replacementp
                    = std::is_same<Vertex, DfgEq>::value
                          ? new DfgAnd{m_dfg, concatp->fileline(), m_bitDType}
                          : nullptr;
                UASSERT_OBJ(replacementp, vtxp,
                            "Unhandled vertex type in 'tryPushCompareOpThroughConcat': "
                                << vtxp->typeName());
                replacementp->relinkSource<0>(newLhsp);
                replacementp->relinkSource<1>(newRhsp);

                // Replace this vertex
                vtxp->replaceWith(replacementp);
                return true;
            }
        }
        return false;
    }

    template <typename Bitwise>
    bool tryPushBitwiseOpThroughReductions(Bitwise* vtxp) {
        using Reduction = BitwiseToReduction<Bitwise>;

        if (Reduction* const lRedp = vtxp->lhsp()->template cast<Reduction>()) {
            if (Reduction* const rRedp = vtxp->rhsp()->template cast<Reduction>()) {
                DfgVertex* const lSrcp = lRedp->srcp();
                DfgVertex* const rSrcp = rRedp->srcp();
                if (lSrcp->dtypep() == rSrcp->dtypep()) {
                    APPLYING(PUSH_BITWISE_THROUGH_REDUCTION) {
                        FileLine* const flp = vtxp->fileline();
                        Bitwise* const bwp = new Bitwise{m_dfg, flp, lSrcp->dtypep()};
                        bwp->lhsp(lSrcp);
                        bwp->rhsp(rSrcp);
                        Reduction* const redp = new Reduction{m_dfg, flp, m_bitDType};
                        redp->srcp(bwp);
                        vtxp->replaceWith(redp);
                        return true;
                    }
                }
            }
        }

        return false;
    }

    template <typename Reduction>
    void optimizeReduction(Reduction* vtxp) {
        using Bitwise = ReductionToBitwise<Reduction>;

        DfgVertex* const srcp = vtxp->srcp();
        FileLine* const flp = vtxp->fileline();

        // Reduction of 1-bit value
        if (srcp->width() == 1) {
            APPLYING(REMOVE_WIDTH_ONE_REDUCTION) {
                vtxp->replaceWith(srcp);
                return;
            }
        }

        if (DfgCond* const condp = srcp->cast<DfgCond>()) {
            if (condp->thenp()->is<DfgConst>() || condp->elsep()->is<DfgConst>()) {
                APPLYING(PUSH_REDUCTION_THROUGH_COND_WITH_CONST_BRANCH) {
                    // The new 'then' vertex
                    Reduction* const newThenp = new Reduction{m_dfg, flp, m_bitDType};
                    newThenp->srcp(condp->thenp());

                    // The new 'else' vertex
                    Reduction* const newElsep = new Reduction{m_dfg, flp, m_bitDType};
                    newElsep->srcp(condp->elsep());

                    // The replacement Cond vertex
                    DfgCond* const newCondp = new DfgCond{m_dfg, condp->fileline(), m_bitDType};
                    newCondp->condp(condp->condp());
                    newCondp->thenp(newThenp);
                    newCondp->elsep(newElsep);

                    // Replace this vertex
                    vtxp->replaceWith(newCondp);
                    return;
                }
            }
        }

        if (DfgConcat* const concatp = srcp->cast<DfgConcat>()) {
            APPLYING(PUSH_REDUCTION_THROUGH_CONCAT) {
                // Reduce the parts of the concatenation
                Reduction* const lReducep = new Reduction{m_dfg, concatp->fileline(), m_bitDType};
                lReducep->srcp(concatp->lhsp());
                Reduction* const rReducep = new Reduction{m_dfg, concatp->fileline(), m_bitDType};
                rReducep->srcp(concatp->rhsp());

                // Bitwise reduce the results
                DfgVertexWithArity<2>* const replacementp = new Bitwise{m_dfg, flp, m_bitDType};
                replacementp->lhsp(lReducep);
                replacementp->rhsp(rReducep);
                vtxp->replaceWith(replacementp);

                // Optimize the new reductions
                optimizeReduction(lReducep);
                optimizeReduction(rReducep);
                return;
            }
        }

        if (DfgConst* const constp = srcp->cast<DfgConst>()) {
            APPLYING(REPLACE_REDUCTION_OF_CONST) {
                DfgConst* const replacementp = makeZero(flp, 1);
                if VL_CONSTEXPR_CXX17 (std::is_same<Reduction, DfgRedAnd>::value) {
                    replacementp->num().opRedAnd(constp->num());
                } else if VL_CONSTEXPR_CXX17 (std::is_same<Reduction, DfgRedOr>::value) {
                    replacementp->num().opRedOr(constp->num());
                } else {
                    replacementp->num().opRedXor(constp->num());
                }
                vtxp->replaceWith(replacementp);
                return;
            }
        }
    }

    void optimizeShiftRHS(DfgVertexWithArity<2>* vtxp) {
        if (const DfgConcat* const concatp = vtxp->rhsp()->cast<DfgConcat>()) {
            if (concatp->lhsp()->isZero()) {  // Drop redundant zero extension
                APPLYING(REMOVE_REDUNDANT_ZEXT_ON_RHS_OF_SHIFT) {  //
                    vtxp->rhsp(concatp->rhsp());
                }
            }
        }
    }

    // VISIT methods

    void visit(DfgVertex*) override {}

    void visit(DfgExtend* vtxp) override {
        const uint32_t extension = vtxp->width() - vtxp->srcp()->width();
        UASSERT_OBJ(extension > 0, vtxp, "Useless Extend");

        FileLine* const flp = vtxp->fileline();

        // Convert Extend into Concat with zeros. This simplifies other patterns as they only
        // need to handle Concat, which is more generic, and don't need special cases for
        // Extend.
        APPLYING(REPLACE_EXTEND) {
            DfgConcat* const replacementp = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
            replacementp->lhsp(makeZero(flp, extension));
            replacementp->rhsp(vtxp->srcp());
            vtxp->replaceWith(replacementp);
        }
    }

    void visit(DfgNot* vtxp) override {
        UASSERT_OBJ(vtxp->width() == vtxp->srcp()->width(), vtxp,
                    "Mismatched width: " << vtxp->width() << " != " << vtxp->srcp()->width());

        // Not of Cond
        if (DfgCond* const condp = vtxp->srcp()->cast<DfgCond>()) {
            // If at least one of the branches are a constant, push the Not past the Cond
            if (condp->thenp()->is<DfgConst>() || condp->elsep()->is<DfgConst>()) {
                APPLYING(PUSH_NOT_THROUGH_COND) {
                    // The new 'then' vertex
                    DfgNot* const newThenp = new DfgNot{m_dfg, vtxp->fileline(), vtxp->dtypep()};
                    newThenp->srcp(condp->thenp());

                    // The new 'else' vertex
                    DfgNot* const newElsep = new DfgNot{m_dfg, vtxp->fileline(), vtxp->dtypep()};
                    newElsep->srcp(condp->elsep());

                    // The replacement Cond vertex
                    DfgCond* const newCondp
                        = new DfgCond{m_dfg, condp->fileline(), vtxp->dtypep()};
                    newCondp->condp(condp->condp());
                    newCondp->thenp(newThenp);
                    newCondp->elsep(newElsep);

                    // Replace this vertex
                    vtxp->replaceWith(newCondp);
                    return;
                }
            }
        }

        // Not of Not
        if (DfgNot* const notp = vtxp->srcp()->cast<DfgNot>()) {
            UASSERT_OBJ(vtxp->width() == notp->srcp()->width(), vtxp, "Width mismatch");
            APPLYING(REMOVE_NOT_NOT) {
                vtxp->replaceWith(notp->srcp());
                return;
            }
        }

        // Not of Eq
        if (DfgEq* const eqp = vtxp->srcp()->cast<DfgEq>()) {
            APPLYING(REPLACE_NOT_EQ) {
                DfgNeq* const replacementp = new DfgNeq{m_dfg, eqp->fileline(), vtxp->dtypep()};
                replacementp->lhsp(eqp->lhsp());
                replacementp->rhsp(eqp->rhsp());
                vtxp->replaceWith(replacementp);
                return;
            }
        }

        // Not of Neq
        if (DfgNeq* const neqp = vtxp->srcp()->cast<DfgNeq>()) {
            APPLYING(REPLACE_NOT_NEQ) {
                DfgEq* const replacementp = new DfgEq{m_dfg, neqp->fileline(), vtxp->dtypep()};
                replacementp->lhsp(neqp->lhsp());
                replacementp->rhsp(neqp->rhsp());
                vtxp->replaceWith(replacementp);
                return;
            }
        }

        // Not of Const
        if (DfgConst* const constp = vtxp->srcp()->cast<DfgConst>()) {
            APPLYING(REPLACE_NOT_OF_CONST) {
                DfgConst* const replacementp = makeZero(vtxp->fileline(), vtxp->width());
                replacementp->num().opNot(constp->num());
                vtxp->replaceWith(replacementp);
                return;
            }
        }
    }

    void visit(DfgAnd* vtxp) override {
        UASSERT_OBJ(vtxp->width() == vtxp->lhsp()->width(), vtxp, "Mismatched LHS width");
        UASSERT_OBJ(vtxp->width() == vtxp->rhsp()->width(), vtxp, "Mismatched RHS width");

        commutativeBinary(vtxp);
        associativeBinary(vtxp);

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        // Bubble pushing
        if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
            if (DfgNot* const rhsNotp = rhsp->cast<DfgNot>()) {
                APPLYING(REPLACE_AND_OF_NOT_AND_NOT) {
                    DfgOr* const orp = new DfgOr{m_dfg, flp, vtxp->dtypep()};
                    orp->lhsp(lhsNotp->srcp());
                    orp->rhsp(rhsNotp->srcp());
                    DfgNot* const notp = new DfgNot{m_dfg, flp, vtxp->dtypep()};
                    notp->srcp(orp);
                    vtxp->replaceWith(notp);
                    return;
                }
            }
            if (DfgNeq* const rhsNeqp = rhsp->cast<DfgNeq>()) {
                APPLYING(REPLACE_AND_OF_NOT_AND_NEQ) {
                    DfgOr* const orp = new DfgOr{m_dfg, flp, vtxp->dtypep()};
                    orp->lhsp(lhsNotp->srcp());
                    DfgEq* const newRhsp = new DfgEq{m_dfg, rhsp->fileline(), rhsp->dtypep()};
                    newRhsp->lhsp(rhsNeqp->lhsp());
                    newRhsp->rhsp(rhsNeqp->rhsp());
                    orp->rhsp(newRhsp);
                    DfgNot* const notp = new DfgNot{m_dfg, flp, vtxp->dtypep()};
                    notp->srcp(orp);
                    vtxp->replaceWith(notp);
                    return;
                }
            }
        }

        if (DfgConst* const lhsConstp = lhsp->cast<DfgConst>()) {
            if (DfgConst* const rhsConstp = rhsp->cast<DfgConst>()) {
                APPLYING(REPLACE_AND_OF_CONST_AND_CONST) {
                    DfgConst* const replacementp = makeZero(flp, vtxp->width());
                    replacementp->num().opAnd(lhsConstp->num(), rhsConstp->num());
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }

            if (lhsConstp->isZero()) {
                APPLYING(REPLACE_AND_WITH_ZERO) {
                    vtxp->replaceWith(lhsConstp);
                    return;
                }
            }

            if (lhsConstp->isOnes()) {
                APPLYING(REMOVE_AND_WITH_ONES) {
                    vtxp->replaceWith(rhsp);
                    return;
                }
            }

            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushBitwiseOpThroughConcat(vtxp, lhsConstp, rhsConcatp)) return;
            }
        }

        if (tryPushBitwiseOpThroughReductions(vtxp)) return;

        if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
            // ~A & A is all zeroes
            if (lhsNotp->srcp() == rhsp) {
                APPLYING(REPLACE_CONTRADICTORY_AND) {
                    DfgConst* const replacementp = makeZero(flp, vtxp->width());
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }
        }
    }

    void visit(DfgOr* vtxp) override {
        UASSERT_OBJ(vtxp->width() == vtxp->lhsp()->width(), vtxp, "Mismatched LHS width");
        UASSERT_OBJ(vtxp->width() == vtxp->rhsp()->width(), vtxp, "Mismatched RHS width");

        commutativeBinary(vtxp);
        associativeBinary(vtxp);

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        // Bubble pushing
        if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
            if (DfgNot* const rhsNotp = rhsp->cast<DfgNot>()) {
                APPLYING(REPLACE_OR_OF_NOT_AND_NOT) {
                    DfgAnd* const andp = new DfgAnd{m_dfg, flp, vtxp->dtypep()};
                    andp->lhsp(lhsNotp->srcp());
                    andp->rhsp(rhsNotp->srcp());
                    DfgNot* const notp = new DfgNot{m_dfg, flp, vtxp->dtypep()};
                    notp->srcp(andp);
                    vtxp->replaceWith(notp);
                    return;
                }
            }
            if (DfgNeq* const rhsNeqp = rhsp->cast<DfgNeq>()) {
                APPLYING(REPLACE_OR_OF_NOT_AND_NEQ) {
                    DfgAnd* const andp = new DfgAnd{m_dfg, flp, vtxp->dtypep()};
                    andp->lhsp(lhsNotp->srcp());
                    DfgEq* const newRhsp = new DfgEq{m_dfg, rhsp->fileline(), rhsp->dtypep()};
                    newRhsp->lhsp(rhsNeqp->lhsp());
                    newRhsp->rhsp(rhsNeqp->rhsp());
                    andp->rhsp(newRhsp);
                    DfgNot* const notp = new DfgNot{m_dfg, flp, vtxp->dtypep()};
                    notp->srcp(andp);
                    vtxp->replaceWith(notp);
                    return;
                }
            }
        }

        if (DfgConcat* const lhsConcatp = lhsp->cast<DfgConcat>()) {
            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (lhsConcatp->lhsp()->width() == rhsConcatp->lhsp()->width()) {
                    if (lhsConcatp->lhsp()->isZero() && rhsConcatp->rhsp()->isZero()) {
                        APPLYING(REPLACE_OR_OF_CONCAT_ZERO_LHS_AND_CONCAT_RHS_ZERO) {
                            DfgConcat* const replacementp
                                = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                            replacementp->lhsp(rhsConcatp->lhsp());
                            replacementp->rhsp(lhsConcatp->rhsp());
                            vtxp->replaceWith(replacementp);
                            return;
                        }
                    }
                    if (lhsConcatp->rhsp()->isZero() && rhsConcatp->lhsp()->isZero()) {
                        APPLYING(REPLACE_OR_OF_CONCAT_LHS_ZERO_AND_CONCAT_ZERO_RHS) {
                            DfgConcat* const replacementp
                                = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                            replacementp->lhsp(lhsConcatp->lhsp());
                            replacementp->rhsp(rhsConcatp->rhsp());
                            vtxp->replaceWith(replacementp);
                            return;
                        }
                    }
                }
            }
        }

        if (DfgConst* const lhsConstp = lhsp->cast<DfgConst>()) {
            if (DfgConst* const rhsConstp = rhsp->cast<DfgConst>()) {
                APPLYING(REPLACE_OR_OF_CONST_AND_CONST) {
                    DfgConst* const replacementp = makeZero(flp, vtxp->width());
                    replacementp->num().opOr(lhsConstp->num(), rhsConstp->num());
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }

            if (lhsConstp->isZero()) {
                APPLYING(REMOVE_OR_WITH_ZERO) {
                    vtxp->replaceWith(rhsp);
                    return;
                }
            }

            if (lhsConstp->isOnes()) {
                APPLYING(REPLACE_OR_WITH_ONES) {
                    vtxp->replaceWith(lhsp);
                    return;
                }
            }

            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushBitwiseOpThroughConcat(vtxp, lhsConstp, rhsConcatp)) return;
            }
        }

        if (tryPushBitwiseOpThroughReductions(vtxp)) return;

        if (DfgNot* const lhsNotp = lhsp->cast<DfgNot>()) {
            // ~A | A is all ones
            if (lhsNotp->srcp() == rhsp) {
                APPLYING(REPLACE_TAUTOLOGICAL_OR) {
                    DfgConst* const replacementp = makeZero(flp, vtxp->width());
                    replacementp->num().setAllBits1();
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }
        }
    }

    void visit(DfgXor* vtxp) override {
        UASSERT_OBJ(vtxp->width() == vtxp->lhsp()->width(), vtxp, "Mismatched LHS width");
        UASSERT_OBJ(vtxp->width() == vtxp->rhsp()->width(), vtxp, "Mismatched RHS width");

        commutativeBinary(vtxp);
        associativeBinary(vtxp);

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        FileLine* const flp = vtxp->fileline();

        if (DfgConst* const lConstp = lhsp->cast<DfgConst>()) {
            if (lConstp->isZero()) {
                APPLYING(REMOVE_XOR_WITH_ZERO) {
                    vtxp->replaceWith(rhsp);
                    return;
                }
            }
            if (lConstp->isOnes()) {
                APPLYING(REPLACE_XOR_WITH_ONES) {
                    DfgNot* const replacementp = new DfgNot{m_dfg, flp, vtxp->dtypep()};
                    replacementp->srcp(rhsp);
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }
            if (DfgConcat* const rConcatp = rhsp->cast<DfgConcat>()) {
                tryPushBitwiseOpThroughConcat(vtxp, lConstp, rConcatp);
                return;
            }
            if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
                APPLYING(REPLACE_XOR_OF_CONST_AND_CONST) {
                    DfgConst* const replacementp = makeZero(flp, vtxp->width());
                    replacementp->num().opXor(lConstp->num(), rConstp->num());
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }
        }

        if (tryPushBitwiseOpThroughReductions(vtxp)) return;
    }

    void visit(DfgAdd* vtxp) override {
        UASSERT_OBJ(vtxp->width() == vtxp->lhsp()->width(), vtxp, "Mismatched LHS width");
        UASSERT_OBJ(vtxp->width() == vtxp->rhsp()->width(), vtxp, "Mismatched RHS width");

        commutativeBinary(vtxp);
        associativeBinary(vtxp);
    }

    void visit(DfgSub* vtxp) override {
        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();
        UASSERT_OBJ(lhsp->width() == rhsp->width(), vtxp, "Width mismatch");
        UASSERT_OBJ(lhsp->width() == vtxp->width(), vtxp, "Width mismatch");
        if (DfgConst* const rConstp = rhsp->cast<DfgConst>()) {
            if (rConstp->isZero()) {
                APPLYING(REMOVE_SUB_ZERO) {
                    vtxp->replaceWith(lhsp);
                    return;
                }
            }
            if (vtxp->width() == 1 && rConstp->toU32() == 1) {
                APPLYING(REPLACE_SUB_WITH_NOT) {
                    DfgNot* const replacementp = new DfgNot{m_dfg, vtxp->fileline(), m_bitDType};
                    replacementp->srcp(lhsp);
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }
        }
    }

    void visit(DfgShiftL* vtxp) override { optimizeShiftRHS(vtxp); }
    void visit(DfgShiftR* vtxp) override { optimizeShiftRHS(vtxp); }
    void visit(DfgShiftRS* vtxp) override { optimizeShiftRHS(vtxp); }

    void visit(DfgEq* vtxp) override {
        commutativeBinary(vtxp);

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        if (DfgConst* const lhsConstp = lhsp->cast<DfgConst>()) {
            if (DfgConst* const rhsConstp = rhsp->cast<DfgConst>()) {
                APPLYING(REPLACE_EQ_OF_CONST_AND_CONST) {
                    DfgConst* const replacementp = makeZero(vtxp->fileline(), 1);
                    replacementp->num().opEq(lhsConstp->num(), rhsConstp->num());
                    vtxp->replaceWith(replacementp);
                    return;
                }
            }

            if (DfgConcat* const rhsConcatp = rhsp->cast<DfgConcat>()) {
                if (tryPushCompareOpThroughConcat(vtxp, lhsConstp, rhsConcatp)) return;
            }
        }
    }

    void visit(DfgSel* vtxp) override {
        DfgVertex* const fromp = vtxp->fromp();
        DfgConst* const lsbp = vtxp->lsbp()->cast<DfgConst>();
        DfgConst* const widthp = vtxp->widthp()->cast<DfgConst>();
        if (!lsbp || !widthp) return;

        FileLine* const flp = vtxp->fileline();

        UASSERT_OBJ(lsbp->toI32() >= 0, vtxp, "Negative LSB in Sel");

        const uint32_t lsb = lsbp->toU32();
        const uint32_t width = widthp->toU32();
        const uint32_t msb = lsb + width - 1;

        UASSERT_OBJ(width == vtxp->width(), vtxp, "Incorrect Sel width");

        // Full width select, replace with the source.
        if (fromp->width() == width) {
            UASSERT_OBJ(lsb == 0, fromp, "OOPS");
            APPLYING(REMOVE_FULL_WIDTH_SEL) {
                vtxp->replaceWith(fromp);
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
                    vtxp->fromp(rhsp);
                }
            } else if (lsb >= rhsp->width()) {
                // If the select is entirely from the lhs, then replace with sel from lhs
                APPLYING(REMOVE_SEL_FROM_LHS_OF_CONCAT) {
                    vtxp->fromp(lhsp);
                    vtxp->lsbp(makeI32(flp, lsb - rhsp->width()));
                }
            } else if (lsb == 0 || msb == concatp->width() - 1  //
                       || lhsp->is<DfgConst>() || rhsp->is<DfgConst>()) {
                // If the select straddles both sides, but at least one of the sides is wholly
                // selected, or at least one of the sides is a Const, then push the Sel past
                // the Concat
                APPLYING(PUSH_SEL_THROUGH_CONCAT) {
                    const uint32_t rSelWidth = rhsp->width() - lsb;
                    const uint32_t lSelWidth = width - rSelWidth;

                    // The new Lhs vertex
                    DfgSel* const newLhsp = new DfgSel{m_dfg, flp, dtypeForWidth(lSelWidth)};
                    newLhsp->fromp(lhsp);
                    newLhsp->lsbp(makeI32(lsbp->fileline(), 0));
                    newLhsp->widthp(makeI32(widthp->fileline(), lSelWidth));

                    // The new Rhs vertex
                    DfgSel* const newRhsp = new DfgSel{m_dfg, flp, dtypeForWidth(rSelWidth)};
                    newRhsp->fromp(rhsp);
                    newRhsp->lsbp(makeI32(lsbp->fileline(), lsb));
                    newRhsp->widthp(makeI32(widthp->fileline(), rSelWidth));

                    // The replacement Concat vertex
                    DfgConcat* const newConcat
                        = new DfgConcat{m_dfg, concatp->fileline(), vtxp->dtypep()};
                    newConcat->lhsp(newLhsp);
                    newConcat->rhsp(newRhsp);

                    // Replace this vertex
                    vtxp->replaceWith(newConcat);
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
                        vtxp->fromp(repp->srcp());
                        vtxp->lsbp(makeI32(flp, newLsb));
                    }
                }
            }
        }

        // Sel from Not
        if (DfgNot* const notp = fromp->cast<DfgNot>()) {
            // Replace "Sel from Not" with "Not of Sel"
            if (!notp->hasMultipleSinks()) {
                UASSERT_OBJ(notp->srcp()->width() == notp->width(), notp, "Mismatched widths");
                APPLYING(PUSH_SEL_THROUGH_NOT) {
                    // Make Sel select from source of Not
                    vtxp->fromp(notp->srcp());
                    // Add Not after Sel
                    DfgNot* const replacementp
                        = new DfgNot{m_dfg, notp->fileline(), vtxp->dtypep()};
                    vtxp->replaceWith(replacementp);
                    replacementp->srcp(vtxp);
                }
            }
        }

        // Sel from Sel
        if (DfgSel* const selp = fromp->cast<DfgSel>()) {
            UASSERT_OBJ(widthp->toU32() <= selp->width(), vtxp, "Out of bound Sel");
            if (DfgConst* const sourceLsbp = selp->lsbp()->cast<DfgConst>()) {
                UASSERT_OBJ(sourceLsbp->toI32() >= 0, selp, "negative");
                UASSERT_OBJ(selp->widthp()->as<DfgConst>()->toU32() >= widthp->toU32(), selp,
                            "negative");
                APPLYING(REPLACE_SEL_FROM_SEL) {
                    // Make this Sel select from the source of the source Sel
                    vtxp->fromp(selp->fromp());
                    // Adjust LSB
                    vtxp->lsbp(makeI32(flp, lsb + sourceLsbp->toU32()));
                }
            }
        }

        // Sel from Cond
        if (DfgCond* const condp = fromp->cast<DfgCond>()) {
            // If at least one of the branches are a constant, push the select past the cond
            if (condp->thenp()->is<DfgConst>() || condp->elsep()->is<DfgConst>()) {
                APPLYING(PUSH_SEL_THROUGH_COND) {
                    // The new 'then' vertex
                    DfgSel* const newThenp = new DfgSel{m_dfg, flp, vtxp->dtypep()};
                    newThenp->fromp(condp->thenp());
                    newThenp->lsbp(makeI32(lsbp->fileline(), lsb));
                    newThenp->widthp(makeI32(widthp->fileline(), width));

                    // The new 'else' vertex
                    DfgSel* const newElsep = new DfgSel{m_dfg, flp, vtxp->dtypep()};
                    newElsep->fromp(condp->elsep());
                    newElsep->lsbp(makeI32(lsbp->fileline(), lsb));
                    newElsep->widthp(makeI32(widthp->fileline(), width));

                    // The replacement Cond vertex
                    DfgCond* const newCondp
                        = new DfgCond{m_dfg, condp->fileline(), vtxp->dtypep()};
                    newCondp->condp(condp->condp());
                    newCondp->thenp(newThenp);
                    newCondp->elsep(newElsep);

                    // Replace this vertex
                    vtxp->replaceWith(newCondp);
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
                    vtxp->fromp(shiftLp->lhsp());
                    DfgShiftL* const newShiftLp
                        = new DfgShiftL{m_dfg, shiftLp->fileline(), vtxp->dtypep()};
                    vtxp->replaceWith(newShiftLp);
                    newShiftLp->lhsp(vtxp);
                    newShiftLp->rhsp(shiftLp->rhsp());
                }
            }
        }

        // Sel from Const
        if (DfgConst* const constp = fromp->cast<DfgConst>()) {
            APPLYING(REPLACE_SEL_FROM_CONST) {
                DfgConst* const replacementp = makeZero(flp, width);
                replacementp->num().opSel(constp->num(), msb, lsb);
                vtxp->replaceWith(replacementp);
                return;
            }
        }
    }

    void visit(DfgRedOr* vtxp) override { optimizeReduction(vtxp); }
    void visit(DfgRedAnd* vtxp) override { optimizeReduction(vtxp); }
    void visit(DfgRedXor* vtxp) override { optimizeReduction(vtxp); }

    void visit(DfgConcat* vtxp) override {
        UASSERT_OBJ(vtxp->width() == vtxp->lhsp()->width() + vtxp->rhsp()->width(), vtxp,
                    "Incorrect Concat width: " << vtxp->width() << " != " << vtxp->lhsp()->width()
                                               << " + " << vtxp->rhsp()->width());

        DfgVertex* const lhsp = vtxp->lhsp();
        DfgVertex* const rhsp = vtxp->rhsp();

        FileLine* const flp = vtxp->fileline();

        // Make concat trees right leaning (for better CSE opportunities)
        if (DfgConcat* const lConcatp = lhsp->cast<DfgConcat>()) {
            if (!lConcatp->hasMultipleSinks()) {
                APPLYING(RIGHT_LEANING_CONCAT) {
                    const uint32_t topWidth = lConcatp->rhsp()->width() + rhsp->width();
                    DfgConcat* const topp = new DfgConcat{m_dfg, flp, dtypeForWidth(topWidth)};
                    DfgConcat* const botp = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                    topp->rhsp(rhsp);
                    topp->lhsp(lConcatp->rhsp());
                    botp->rhsp(topp);
                    botp->lhsp(lConcatp->lhsp());
                    vtxp->replaceWith(botp);
                    return;
                }
            }
        }

        {
            const auto joinConsts
                = [this](DfgConst* lConstp, DfgConst* rConstp, FileLine* flp) -> DfgConst* {
                DfgConst* const newConstp = makeZero(flp, lConstp->width() + rConstp->width());
                newConstp->num().opSelInto(rConstp->num(), 0, rConstp->width());
                newConstp->num().opSelInto(lConstp->num(), rConstp->width(), lConstp->width());
                return newConstp;
            };

            DfgConst* const lConstp = lhsp->cast<DfgConst>();
            DfgConst* const rConstp = rhsp->cast<DfgConst>();

            if (lConstp && rConstp) {
                APPLYING(REPLACE_CONCAT_OF_CONSTS) {
                    vtxp->replaceWith(joinConsts(lConstp, rConstp, flp));
                    return;
                }
            }

            if (lConstp) {
                if (DfgConcat* const rConcatp = rhsp->cast<DfgConcat>()) {
                    if (DfgConst* const rlConstp = rConcatp->lhsp()->cast<DfgConst>()) {
                        APPLYING(REPLACE_NESTED_CONCAT_OF_CONSTS_ON_LHS) {
                            DfgConst* const joinedConstp = joinConsts(lConstp, rlConstp, flp);
                            DfgConcat* const replacementp
                                = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                            replacementp->lhsp(joinedConstp);
                            replacementp->rhsp(rConcatp->rhsp());
                            vtxp->replaceWith(replacementp);
                            return;
                        }
                    }
                }

                if (lConstp->isZero()) {
                    if (DfgSel* const rSelp = rhsp->cast<DfgSel>()) {
                        if (DfgConst* const rSelLsbConstp = rSelp->lsbp()->cast<DfgConst>()) {
                            if (vtxp->width() == rSelp->fromp()->width()
                                && rSelLsbConstp->toU32() == lConstp->width()) {
                                const uint32_t rSelWidth
                                    = rSelp->widthp()->as<DfgConst>()->toU32();
                                UASSERT_OBJ(lConstp->width() + rSelWidth == vtxp->width(), vtxp,
                                            "Inconsistent");
                                APPLYING(REPLACE_CONCAT_ZERO_AND_SEL_TOP_WITH_SHIFTR) {
                                    DfgShiftR* const replacementp
                                        = new DfgShiftR{m_dfg, flp, vtxp->dtypep()};
                                    replacementp->lhsp(rSelp->fromp());
                                    replacementp->rhsp(makeI32(flp, lConstp->width()));
                                    vtxp->replaceWith(replacementp);
                                    return;
                                }
                            }
                        }
                    }
                }
            }

            if (rConstp) {
                if (DfgConcat* const lConcatp = lhsp->cast<DfgConcat>()) {
                    if (DfgConst* const lrConstp = lConcatp->rhsp()->cast<DfgConst>()) {
                        APPLYING(REPLACE_NESTED_CONCAT_OF_CONSTS_ON_RHS) {
                            DfgConst* const joinedConstp = joinConsts(lrConstp, rConstp, flp);
                            DfgConcat* const replacementp
                                = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                            replacementp->lhsp(lConcatp->lhsp());
                            replacementp->rhsp(joinedConstp);
                            vtxp->replaceWith(replacementp);
                            return;
                        }
                    }
                }

                if (rConstp->isZero()) {
                    if (DfgSel* const lSelp = lhsp->cast<DfgSel>()) {
                        if (DfgConst* const lSelLsbConstp = lSelp->lsbp()->cast<DfgConst>()) {
                            if (vtxp->width() == lSelp->fromp()->width()
                                && lSelLsbConstp->toU32() == 0) {
                                const uint32_t lSelWidth
                                    = lSelp->widthp()->as<DfgConst>()->toU32();
                                UASSERT_OBJ(lSelWidth + rConstp->width() == vtxp->width(), vtxp,
                                            "Inconsistent");
                                APPLYING(REPLACE_CONCAT_SEL_BOTTOM_AND_ZERO_WITH_SHIFTL) {
                                    DfgShiftL* const replacementp
                                        = new DfgShiftL{m_dfg, flp, vtxp->dtypep()};
                                    replacementp->lhsp(lSelp->fromp());
                                    replacementp->rhsp(makeI32(flp, rConstp->width()));
                                    vtxp->replaceWith(replacementp);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }

        {
            DfgNot* const lNot = lhsp->cast<DfgNot>();
            DfgNot* const rNot = rhsp->cast<DfgNot>();
            if (lNot && rNot) {
                APPLYING(PUSH_CONCAT_THROUGH_NOTS) {
                    vtxp->lhsp(lNot->srcp());
                    vtxp->rhsp(rNot->srcp());
                    DfgNot* const replacementp = new DfgNot{m_dfg, flp, vtxp->dtypep()};
                    vtxp->replaceWith(replacementp);
                    replacementp->srcp(vtxp);
                    return;
                }
            }
        }

        {
            const auto joinSels = [this](DfgSel* lSelp, DfgSel* rSelp, FileLine* flp) -> DfgSel* {
                DfgConst* const lLsbp = lSelp->lsbp()->cast<DfgConst>();
                DfgConst* const lWidthp = lSelp->widthp()->cast<DfgConst>();
                DfgConst* const rLsbp = rSelp->lsbp()->cast<DfgConst>();
                DfgConst* const rWidthp = rSelp->widthp()->cast<DfgConst>();
                if (lLsbp && lWidthp && rLsbp && rWidthp) {
                    if (lSelp->fromp()->equals(*rSelp->fromp())) {
                        if (lLsbp->toU32() == rLsbp->toU32() + rWidthp->toU32()) {
                            // Two consecutive Sels, make a single Sel.
                            const uint32_t width = lWidthp->toU32() + rWidthp->toU32();
                            AstNodeDType* const dtypep = dtypeForWidth(width);
                            DfgSel* const joinedSelp = new DfgSel{m_dfg, flp, dtypep};
                            joinedSelp->fromp(rSelp->fromp());
                            joinedSelp->lsbp(rSelp->lsbp());
                            joinedSelp->widthp(makeI32(flp, width));
                            return joinedSelp;
                        }
                    }
                }
                return nullptr;
            };

            DfgSel* const lSelp = lhsp->cast<DfgSel>();
            DfgSel* const rSelp = rhsp->cast<DfgSel>();
            if (lSelp && rSelp) {
                if (DfgSel* const jointSelp = joinSels(lSelp, rSelp, flp)) {
                    APPLYING(REMOVE_CONCAT_OF_ADJOINING_SELS) {
                        vtxp->replaceWith(jointSelp);
                        return;
                    }
                }
            }
            if (lSelp) {
                if (DfgConcat* const rConcatp = rhsp->cast<DfgConcat>()) {
                    if (DfgSel* const rlSelp = rConcatp->lhsp()->cast<DfgSel>()) {
                        if (DfgSel* const jointSelp = joinSels(lSelp, rlSelp, flp)) {
                            APPLYING(REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_LHS) {
                                DfgConcat* const replacementp
                                    = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                                replacementp->lhsp(jointSelp);
                                replacementp->rhsp(rConcatp->rhsp());
                                vtxp->replaceWith(replacementp);
                                return;
                            }
                        }
                    }
                }
            }
            if (rSelp) {
                if (DfgConcat* const lConcatp = lhsp->cast<DfgConcat>()) {
                    if (DfgSel* const lrlSelp = lConcatp->rhsp()->cast<DfgSel>()) {
                        if (DfgSel* const jointSelp = joinSels(lrlSelp, rSelp, flp)) {
                            APPLYING(REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_RHS) {
                                DfgConcat* const replacementp
                                    = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                                replacementp->lhsp(lConcatp->lhsp());
                                replacementp->rhsp(jointSelp);
                                vtxp->replaceWith(replacementp);
                                return;
                            }
                        }
                    }
                }
            }
        }
    }

    void visit(DfgCond* vtxp) override {
        DfgVertex* const condp = vtxp->condp();
        DfgVertex* const thenp = vtxp->thenp();
        DfgVertex* const elsep = vtxp->elsep();
        UASSERT_OBJ(vtxp->width() == thenp->width(), vtxp, "Width mismatch");
        UASSERT_OBJ(vtxp->width() == elsep->width(), vtxp, "Width mismatch");

        if (condp->width() != 1) return;

        FileLine* const flp = vtxp->fileline();

        if (condp->isOnes()) {
            APPLYING(REMOVE_COND_WITH_TRUE_CONDITION) {
                vtxp->replaceWith(thenp);
                return;
            }
        }

        if (condp->isZero()) {
            APPLYING(REMOVE_COND_WITH_FALSE_CONDITION) {
                vtxp->replaceWith(elsep);
                return;
            }
        }

        if (DfgNot* const condNotp = condp->cast<DfgNot>()) {
            APPLYING(SWAP_COND_WITH_NOT_CONDITION) {
                vtxp->condp(condNotp->srcp());
                vtxp->thenp(elsep);
                vtxp->elsep(thenp);
                visit(vtxp);
                return;
            }
        }

        if (DfgNeq* const condNeqp = condp->cast<DfgNeq>()) {
            APPLYING(SWAP_COND_WITH_NEQ_CONDITION) {
                DfgEq* const newCondp = new DfgEq{m_dfg, condp->fileline(), condp->dtypep()};
                newCondp->lhsp(condNeqp->lhsp());
                newCondp->rhsp(condNeqp->rhsp());
                vtxp->condp(newCondp);
                vtxp->thenp(elsep);
                vtxp->elsep(thenp);
                visit(vtxp);
                return;
            }
        }

        if (DfgNot* const thenNotp = thenp->cast<DfgNot>()) {
            if (DfgNot* const elseNotp = elsep->cast<DfgNot>()) {
                APPLYING(PULL_NOTS_THROUGH_COND) {
                    DfgNot* const replacementp
                        = new DfgNot{m_dfg, thenp->fileline(), vtxp->dtypep()};
                    vtxp->thenp(thenNotp->srcp());
                    vtxp->elsep(elseNotp->srcp());
                    vtxp->replaceWith(replacementp);
                    replacementp->srcp(vtxp);
                    return;
                }
            }
        }

        if (vtxp->width() > 1) {
            // 'cond ? a + 1 : a' -> 'a + cond'
            if (DfgAdd* const thenAddp = thenp->cast<DfgAdd>()) {
                if (DfgConst* const constp = thenAddp->lhsp()->cast<DfgConst>()) {
                    if (constp->toI32() == 1) {
                        if (thenAddp->rhsp() == elsep) {
                            APPLYING(REPLACE_COND_INC) {
                                DfgConcat* const extp = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                                extp->rhsp(condp);
                                extp->lhsp(makeZero(flp, vtxp->width() - 1));
                                FileLine* const thenFlp = thenAddp->fileline();
                                DfgAdd* const addp = new DfgAdd{m_dfg, thenFlp, vtxp->dtypep()};
                                addp->lhsp(thenAddp->rhsp());
                                addp->rhsp(extp);
                                vtxp->replaceWith(addp);
                                return;
                            }
                        }
                    }
                }
            }
            // 'cond ? a - 1 : a' -> 'a - cond'
            if (DfgSub* const thenSubp = thenp->cast<DfgSub>()) {
                if (DfgConst* const constp = thenSubp->rhsp()->cast<DfgConst>()) {
                    if (constp->toI32() == 1) {
                        if (thenSubp->lhsp() == elsep) {
                            APPLYING(REPLACE_COND_DEC) {
                                DfgConcat* const extp = new DfgConcat{m_dfg, flp, vtxp->dtypep()};
                                extp->rhsp(condp);
                                extp->lhsp(makeZero(flp, vtxp->width() - 1));
                                FileLine* const thenFlp = thenSubp->fileline();
                                DfgSub* const subp = new DfgSub{m_dfg, thenFlp, vtxp->dtypep()};
                                subp->lhsp(thenSubp->lhsp());
                                subp->rhsp(extp);
                                vtxp->replaceWith(subp);
                                return;
                            }
                        }
                    }
                }
            }
        }

        if (vtxp->width() == 1) {
            AstNodeDType* const dtypep = vtxp->dtypep();
            if (thenp->isZero()) {  // a ? 0 : b becomes ~a & b
                APPLYING(REPLACE_COND_WITH_THEN_BRANCH_ZERO) {
                    DfgAnd* const repalcementp = new DfgAnd{m_dfg, flp, dtypep};
                    DfgNot* const notp = new DfgNot{m_dfg, flp, dtypep};
                    notp->srcp(condp);
                    repalcementp->lhsp(notp);
                    repalcementp->rhsp(elsep);
                    vtxp->replaceWith(repalcementp);
                    return;
                }
            }
            if (thenp->isOnes()) {  // a ? 1 : b becomes a | b
                APPLYING(REPLACE_COND_WITH_THEN_BRANCH_ONES) {
                    DfgOr* const repalcementp = new DfgOr{m_dfg, flp, dtypep};
                    repalcementp->lhsp(condp);
                    repalcementp->rhsp(elsep);
                    vtxp->replaceWith(repalcementp);
                    return;
                }
            }
            if (elsep->isZero()) {  // a ? b : 0 becomes a & b
                APPLYING(REPLACE_COND_WITH_ELSE_BRANCH_ZERO) {
                    DfgAnd* const repalcementp = new DfgAnd{m_dfg, flp, dtypep};
                    repalcementp->lhsp(condp);
                    repalcementp->rhsp(thenp);
                    vtxp->replaceWith(repalcementp);
                    return;
                }
            }
            if (elsep->isOnes()) {  // a ? b : 1 becomes ~a | b
                APPLYING(REPLACE_COND_WITH_ELSE_BRANCH_ONES) {
                    DfgOr* const repalcementp = new DfgOr{m_dfg, flp, dtypep};
                    DfgNot* const notp = new DfgNot{m_dfg, flp, dtypep};
                    notp->srcp(condp);
                    repalcementp->lhsp(notp);
                    repalcementp->rhsp(thenp);
                    vtxp->replaceWith(repalcementp);
                    return;
                }
            }
        }
    }

    void visit(DfgArraySel* vtxp) override {
        if (DfgConst* const idxp = vtxp->bitp()->cast<DfgConst>()) {
            if (DfgVarArray* const varp = vtxp->fromp()->cast<DfgVarArray>()) {
                const uint32_t idx = idxp->toU32();
                if (DfgVertex* const driverp = varp->driverAt(idx)) {
                    APPLYING(INLINE_ARRAYSEL) {
                        vtxp->replaceWith(driverp);
                        return;
                    }
                }
            }
        }
    }

    void visit(DfgVarPacked* vtxp) override {
        // Inline variables fully driven by the logic represented by the DFG
        if (vtxp->hasSinks() && vtxp->isDrivenFullyByDfg()) {
            APPLYING(INLINE_VAR) {
                // Make consumers of the DfgVar consume the driver directly
                DfgVertex* const driverp = vtxp->source(0);
                vtxp->forEachSinkEdge([=](DfgEdge& edge) { edge.relinkSource(driverp); });
            }
        }
    }

#undef APPLYING

    // Process one vertex. Return true if graph changed
    bool processVertex(DfgVertex& vtx) {
        // Keep DfgVertexLValue vertices in this pass. We will remove them later if they become
        // redundant. We want to keep the original variables for non-var vertices that drive
        // multiple sinks (otherwise we would need to introduce a temporary, but it is better for
        // debugging to keep the original variable name, if one is available), so we can't remove
        // redundant variables here.
        const bool keep = vtx.is<DfgVarPacked>() || vtx.is<DfgVarArray>();

        // If it has no sinks (unused), we can remove it
        if (!keep && !vtx.hasSinks()) {
            vtx.unlinkDelete(m_dfg);
            return true;
        }

        // Transform node
        m_changed = false;
        iterate(&vtx);

        // If it became unused, we can remove it
        if (!keep && !vtx.hasSinks()) {
            UASSERT_OBJ(m_changed, &vtx, "'m_changed' must be set if node became unused");
            vtx.unlinkDelete(m_dfg);
            return true;
        }

        // Return the changed status
        return m_changed;
    }

    V3DfgPeephole(DfgGraph& dfg, V3DfgPeepholeContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {}

public:
    static void apply(DfgGraph& dfg, V3DfgPeepholeContext& ctx) {
        V3DfgPeephole visitor{dfg, ctx};
        dfg.runToFixedPoint([&](DfgVertex& vtx) { return visitor.processVertex(vtx); });
    }
};

void V3DfgPasses::peephole(DfgGraph& dfg, V3DfgPeepholeContext& ctx) {
    V3DfgPeephole::apply(dfg, ctx);
}
