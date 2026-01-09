// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: DfgGraph common sub-expression elimination (CSE)
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class V3DfgCse final {
    // TYPES
    using VertexPair = std::pair<const DfgVertex*, const DfgVertex*>;
    struct VertexPairHash final {
        size_t operator()(const VertexPair& pair) const {
            V3Hash hash;
            hash += pair.first;
            hash += pair.second;
            return hash.value();
        }
    };

    // STATE
    // The graph being processed
    DfgGraph& m_dfg;
    // Cache for vertex hashes
    DfgUserMap<V3Hash> m_hashCache = m_dfg.makeUserMap<V3Hash>();
    // Cache for vertex equality
    std::unordered_map<VertexPair, uint8_t, VertexPairHash> m_equivalentCache;

    // METHODS
    // Returns hash of vertex dependent on information internal to the vertex
    static V3Hash vertexSelfHash(const DfgVertex& vtx) {
        switch (vtx.type()) {
        // Unhandled vertices
        case VDfgType::Logic:  // LCOV_EXCL_START
        case VDfgType::Unresolved:  // LCOV_EXCL_STOP
            vtx.v3fatalSrc("Should not have reached CSE");

        // Special vertices
        case VDfgType::Const:  // LCOV_EXCL_START
        case VDfgType::VarArray:
        case VDfgType::VarPacked:  // LCOV_EXCL_STOP
            vtx.v3fatalSrc("Hash should have been pre-computed");

        // Vertices with internal information
        case VDfgType::Sel: return V3Hash{vtx.as<DfgSel>()->lsb()};

        case VDfgType::SpliceArray:
        case VDfgType::SplicePacked: {
            V3Hash hash;
            vtx.as<DfgVertexSplice>()->foreachDriver([&](const DfgVertex&, uint32_t lo) {
                hash += lo;
                return false;
            });
            return hash;
        }

        // Vertices with no internal information
        case VDfgType::Mux:
        case VDfgType::UnitArray: return V3Hash{};

        // Generated classes - none of them have internal information
        case VDfgType::Add:
        case VDfgType::And:
        case VDfgType::ArraySel:
        case VDfgType::BufIf1:
        case VDfgType::Concat:
        case VDfgType::Cond:
        case VDfgType::Div:
        case VDfgType::DivS:
        case VDfgType::Eq:
        case VDfgType::EqCase:
        case VDfgType::EqWild:
        case VDfgType::Extend:
        case VDfgType::ExtendS:
        case VDfgType::Gt:
        case VDfgType::GtS:
        case VDfgType::Gte:
        case VDfgType::GteS:
        case VDfgType::LogAnd:
        case VDfgType::LogEq:
        case VDfgType::LogIf:
        case VDfgType::LogNot:
        case VDfgType::LogOr:
        case VDfgType::Lt:
        case VDfgType::LtS:
        case VDfgType::Lte:
        case VDfgType::LteS:
        case VDfgType::ModDiv:
        case VDfgType::ModDivS:
        case VDfgType::Mul:
        case VDfgType::MulS:
        case VDfgType::Negate:
        case VDfgType::Neq:
        case VDfgType::NeqCase:
        case VDfgType::NeqWild:
        case VDfgType::Not:
        case VDfgType::Or:
        case VDfgType::Pow:
        case VDfgType::PowSS:
        case VDfgType::PowSU:
        case VDfgType::PowUS:
        case VDfgType::RedAnd:
        case VDfgType::RedOr:
        case VDfgType::RedXor:
        case VDfgType::Replicate:
        case VDfgType::ShiftL:
        case VDfgType::ShiftR:
        case VDfgType::ShiftRS:
        case VDfgType::StreamL:
        case VDfgType::StreamR:
        case VDfgType::Sub:
        case VDfgType::Xor: return V3Hash{};
        }
        VL_UNREACHABLE;
    }

    // Returns hash of vertex dependent on and all its input
    V3Hash vertexHash(DfgVertex& vtx) {
        V3Hash& result = m_hashCache[vtx];
        if (!result.value()) {
            V3Hash hash{vertexSelfHash(vtx)};
            // Variables are defined by themselves, so there is no need to hash them further
            // (especially the sources). This enables sound hashing of graphs circular only through
            // variables, which we rely on.
            if (!vtx.is<DfgVertexVar>()) {
                hash += vtx.type();
                hash += vtx.size();
                vtx.foreachSource([&](DfgVertex& src) {
                    hash += vertexHash(src);
                    return false;
                });
            }
            result = hash;
        }
        return result;
    }

    // Compare 'a' and 'b' for equivalence based on their internal information only
    bool vertexSelfEquivalent(const DfgVertex& a, const DfgVertex& b) {
        // Note: 'a' and 'b' are of the same Vertex type, data type, and have
        // the same number of inputs with matching types. This is established
        // by 'vertexEquivalent'.
        switch (a.type()) {
        // Unhandled vertices
        case VDfgType::Logic:  // LCOV_EXCL_START
        case VDfgType::Unresolved:  // LCOV_EXCL_STOP
            a.v3fatalSrc("Should not have reached CSE");

        // Special vertices
        case VDfgType::Const: return a.as<DfgConst>()->num().isCaseEq(b.as<DfgConst>()->num());

        case VDfgType::VarArray:
        case VDfgType::VarPacked:
            return false;  // CSE does not combine variables

        // Vertices with internal information
        case VDfgType::Sel: return a.as<DfgSel>()->lsb() == b.as<DfgSel>()->lsb();

        case VDfgType::SpliceArray:
        case VDfgType::SplicePacked: {
            const DfgVertexSplice* const ap = a.as<DfgVertexSplice>();
            // Gather indices of drivers of 'a'
            std::vector<uint32_t> aLo;
            aLo.reserve(ap->nInputs());
            ap->foreachDriver([&](const DfgVertex&, uint32_t lo) {
                aLo.push_back(lo);
                return false;
            });
            // Compare indices of drivers of 'b'
            uint32_t* aLop = aLo.data();
            return !b.as<DfgVertexSplice>()->foreachDriver(
                [&](const DfgVertex&, uint32_t lo) { return *aLop++ != lo; });
        }

        // Vertices with no internal information
        case VDfgType::Mux:
        case VDfgType::UnitArray: return true;

        // Generated classes - none of them have internal information
        case VDfgType::Add:
        case VDfgType::And:
        case VDfgType::ArraySel:
        case VDfgType::BufIf1:
        case VDfgType::Concat:
        case VDfgType::Cond:
        case VDfgType::Div:
        case VDfgType::DivS:
        case VDfgType::Eq:
        case VDfgType::EqCase:
        case VDfgType::EqWild:
        case VDfgType::Extend:
        case VDfgType::ExtendS:
        case VDfgType::Gt:
        case VDfgType::GtS:
        case VDfgType::Gte:
        case VDfgType::GteS:
        case VDfgType::LogAnd:
        case VDfgType::LogEq:
        case VDfgType::LogIf:
        case VDfgType::LogNot:
        case VDfgType::LogOr:
        case VDfgType::Lt:
        case VDfgType::LtS:
        case VDfgType::Lte:
        case VDfgType::LteS:
        case VDfgType::ModDiv:
        case VDfgType::ModDivS:
        case VDfgType::Mul:
        case VDfgType::MulS:
        case VDfgType::Negate:
        case VDfgType::Neq:
        case VDfgType::NeqCase:
        case VDfgType::NeqWild:
        case VDfgType::Not:
        case VDfgType::Or:
        case VDfgType::Pow:
        case VDfgType::PowSS:
        case VDfgType::PowSU:
        case VDfgType::PowUS:
        case VDfgType::RedAnd:
        case VDfgType::RedOr:
        case VDfgType::RedXor:
        case VDfgType::Replicate:
        case VDfgType::ShiftL:
        case VDfgType::ShiftR:
        case VDfgType::ShiftRS:
        case VDfgType::StreamL:
        case VDfgType::StreamR:
        case VDfgType::Sub:
        case VDfgType::Xor: return true;
        }
        VL_UNREACHABLE;
    }

    // Compares 'a' and 'b' for equivalence
    bool vertexEquivalent(const DfgVertex& a, const DfgVertex& b) {
        // If same vertex, then equal
        if (&a == &b) return true;

        // If different type, then not equal
        if (a.type() != b.type()) return false;

        // If different data type, then not equal
        if (a.dtype() != b.dtype()) return false;

        // If different number of inputs, then not equal
        if (a.nInputs() != b.nInputs()) return false;

        // Check vertex specifics
        if (!vertexSelfEquivalent(a, b)) return false;

        // Check sources
        const VertexPair key = (&a < &b) ? std::make_pair(&a, &b) : std::make_pair(&b, &a);
        // The recursive invocation can cause a re-hash but that will not invalidate references
        uint8_t& result = m_equivalentCache[key];
        if (!result) {
            const bool equal = [&]() {
                for (size_t i = 0; i < a.nInputs(); ++i) {
                    const DfgVertex* const ap = a.inputp(i);
                    const DfgVertex* const bp = b.inputp(i);
                    if (!ap && !bp) continue;
                    if (!ap || !bp) return false;
                    if (!vertexEquivalent(*ap, *bp)) return false;
                }
                return true;
            }();
            result = (static_cast<uint8_t>(equal) << 1) | 1;
        }
        return result >> 1;
    }

    V3DfgCse(DfgGraph& dfg, V3DfgCseContext& ctx)
        : m_dfg{dfg} {
        std::unordered_map<V3Hash, std::vector<DfgVertex*>> verticesWithEqualHashes;
        verticesWithEqualHashes.reserve(dfg.size());

        // Pre-hash variables, these are all unique, so just set their hash to a unique value
        uint32_t varHash = 0;
        for (const DfgVertexVar& vtx : dfg.varVertices()) m_hashCache[vtx] = V3Hash{++varHash};

        // Similarly pre-hash constants for speed. While we don't combine constants, we do want
        // expressions using the same constants to be combined, so we do need to hash equal
        // constants to equal values.
        for (DfgConst* const vtxp : dfg.constVertices().unlinkable()) {
            // Delete unused constants while we are at it.
            if (!vtxp->hasSinks()) {
                VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
                continue;
            }
            m_hashCache[vtxp] = vtxp->num().toHash() + varHash;
        }

        // Combine operation vertices
        for (DfgVertex* const vtxp : dfg.opVertices().unlinkable()) {
            // Delete unused nodes while we are at it.
            if (!vtxp->hasSinks()) {
                vtxp->unlinkDelete(dfg);
                continue;
            }
            std::vector<DfgVertex*>& vec = verticesWithEqualHashes[vertexHash(*vtxp)];
            bool replaced = false;
            for (DfgVertex* const candidatep : vec) {
                if (vertexEquivalent(*candidatep, *vtxp)) {
                    ++ctx.m_eliminated;
                    vtxp->replaceWith(candidatep);
                    VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
                    replaced = true;
                    break;
                }
            }
            if (replaced) continue;
            vec.push_back(vtxp);
        }
    }

public:
    static void apply(DfgGraph& dfg, V3DfgCseContext& ctx) {
        V3DfgCse{dfg, ctx};
        // Prune unused nodes
        V3DfgPasses::removeUnused(dfg);
    }
};

void V3DfgPasses::cse(DfgGraph& dfg, V3DfgCseContext& ctx) { V3DfgCse::apply(dfg, ctx); }
