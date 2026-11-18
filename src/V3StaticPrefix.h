// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Longest static prefixes of expressions
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
// The longest static prefix of an expression (IEEE 1800-2023 11.5.3) is the
// part of a variable it selects that is known after elaboration. For example,
// the longest static prefix of 'a.b[i][2]' is 'a.b'.
//
// Prefixes are represented as ranges in a flattened index space of 'grains',
// defined for all types:
//
//   - A packed type has one grain per bit.
//   - An unpacked array has the grains of its elements, in order.
//   - An unpacked struct has the grains of its members, in order.
//   - Any other type (unpacked unions, strings, dynamically sized types,
//     etc.) is a single grain.
//
// Two prefixes of a variable then overlap when their ranges do.
//
//*************************************************************************

#ifndef VERILATOR_V3STATICPREFIX_H_
#define VERILATOR_V3STATICPREFIX_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <algorithm>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

//######################################################################
// Gather the longest static prefixes

class V3StaticPrefix final : public VNVisitorConst {
    // TYPES
    // A longest static prefix: the grains [m_lo, m_hi) of a variable
    struct Prefix final {
        uint64_t m_lo;  // First grain
        uint64_t m_hi;  // One past the last grain
    };

    // NODE STATE
    // AstNodeDType::user1()   -> uint64_t. Number of grains of the data type, zero until computed
    // AstMemberDType::user2() -> uint64_t. First grain of the member in its struct
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // STATE
    // Longest static prefixes read and written, by variable
    std::unordered_map<const AstVarScope*, std::vector<Prefix>> m_rds;
    std::unordered_map<const AstVarScope*, std::vector<Prefix>> m_wrs;

    // METHODS

    // Number of grains in the given data type
    static uint64_t nGrains(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (!dtypep->user1()) {
            dtypep->user1([&]() -> uint64_t {
                if (dtypep->isIntegralOrPacked()) {
                    return std::max<uint64_t>(dtypep->width(), 1);
                }
                if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
                    return adtypep->elementsConst() * nGrains(adtypep->subDTypep());
                }
                if (AstStructDType* const sdtypep = VN_CAST(dtypep, StructDType)) {
                    uint64_t result = 0;
                    for (AstMemberDType* const memberp : sdtypep->memberspList()) {
                        memberp->user2(result);
                        result += nGrains(memberp->subDTypep());
                    }
                    return result;
                }
                // Other data types are treated as whole (single grain)
                return 1;
            }());
        }
        return dtypep->user1();
    }

    // First grain of the given member of an unpacked structure
    static uint64_t firstGrain(const AstMemberDType* memberp) {
        nGrains(memberp->parentp());  // Computes the first grain of the members
        return memberp->user2();
    }

    // Record the longest static prefix of an expression, walking down its static selects to the
    // variable they select from. If the expression is neither, visit its operands, which will
    // record the wider static prefixes under them.
    void record(AstNodeExpr* exprp) {
        // The grains [lo, hi) of 'exprp' accessed, less any part statically out of range
        uint64_t lo = 0;
        uint64_t hi = std::numeric_limits<uint64_t>::max();
        // Given 'exprp' is a select of the 'width' grains at 'offset' of the expression
        // it selects from, convert current [lo, hi) to grains of the selected from expression.
        // Any part past 'width' is selected out of range, and is dropped so it does not alias
        // the grains following 'exprp'.
        const auto select = [&](uint64_t offset, uint64_t width) -> void {
            lo = offset + std::min(lo, width);
            hi = offset + std::min(hi, width);
        };
        while (true) {
            if (const AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
                const AstVarScope* const vscp = refp->varScopep();
                select(0, nGrains(vscp->dtypep()));
                const Prefix prefix{lo, hi};
                if (refp->access().isReadOrRW()) m_rds[vscp].emplace_back(prefix);
                if (refp->access().isWriteOrRW() && !vscp->varp()->ignoreSchedWrite()) {
                    m_wrs[vscp].emplace_back(prefix);
                }
                return;
            } else if (const AstSel* const selp = VN_CAST(exprp, Sel)) {
                AstNodeExpr* const fromp = selp->fromp();
                const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
                if (lsbp && lsbp->num().fitsInUInt()) {
                    select(lsbp->num().toUInt(), selp->widthConst());
                    exprp = fromp;
                    continue;
                }
            } else if (const AstArraySel* const selp = VN_CAST(exprp, ArraySel)) {
                AstNodeExpr* const fromp = selp->fromp();
                const AstConst* const idxp = VN_CAST(selp->bitp(), Const);
                if (idxp && idxp->num().fitsInUInt()) {
                    const uint64_t grains = nGrains(selp->dtypep());
                    select(idxp->num().toUInt() * grains, grains);
                    exprp = fromp;
                    continue;
                }
            } else if (const AstStructSel* const selp = VN_CAST(exprp, StructSel)) {
                AstNodeExpr* const fromp = selp->fromp();
                const AstMemberDType* const memberp = selp->memberp();
                if (VN_IS(memberp->parentp(), StructDType)) {
                    select(firstGrain(memberp), nGrains(memberp->subDTypep()));
                    exprp = fromp;
                    continue;
                }
            }
            // The longest static prefix, if any, is below
            iterateChildrenConst(exprp);
            return;
        }
    }

    // VISITORS
    void visit(AstVarRef* nodep) override { record(nodep); }
    void visit(AstSel* nodep) override { record(nodep); }
    void visit(AstArraySel* nodep) override { record(nodep); }
    void visit(AstStructSel* nodep) override { record(nodep); }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTOR
    V3StaticPrefix() = default;

    // The variables of which the given node reads grains that it does not write.
    // Writes to variables with ignoreSchedWrite() do not count.
    std::unordered_set<const AstVarScope*> readNotWritten(AstNode* nodep) {
        m_rds.clear();
        m_wrs.clear();
        iterateConst(nodep);
        std::unordered_set<const AstVarScope*> result;
        for (const auto& pair : m_rds) {
            // Sort and merge the prefixes written, in place
            std::vector<Prefix>& writes = m_wrs[pair.first];
            if (!writes.empty()) {
                std::sort(writes.begin(), writes.end(), [](const Prefix& a, const Prefix& b) {  //
                    return a.m_lo < b.m_lo;
                });
                size_t last = 0;  // Index of the last merged prefix
                for (size_t i = 1; i < writes.size(); ++i) {
                    if (writes[last].m_hi >= writes[i].m_lo) {
                        // Overlaps or adjoins, merge it
                        writes[last].m_hi = std::max(writes[last].m_hi, writes[i].m_hi);
                    } else {
                        // Does not overlap, keep new prefix
                        writes[++last] = writes[i];
                    }
                }
                writes.resize(last + 1);
            }
            // The merged writes are disjoint, so a read can only be fully covered by at most one.
            // If any read is not covered, the variable is read but not written, so is returned.
            for (const Prefix& read : pair.second) {
                if (read.m_lo == read.m_hi) continue;  // Out of range
                const auto it = std::lower_bound(writes.begin(), writes.end(), read.m_hi,
                                                 [](const Prefix& prefix, uint64_t hi) {  //
                                                     return prefix.m_hi < hi;
                                                 });
                if (it == writes.end() || it->m_lo > read.m_lo) {
                    result.emplace(pair.first);
                    break;
                }
            }
        }
        return result;
    }
};

#endif  // Guard
