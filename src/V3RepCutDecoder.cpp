// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Native decoder cache recognition
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************
//
// Recognize the exact private cache shapes emitted by the ordinary DFG decoder
// pass. These caches retain native scheduling and write no HDL state, so they
// do not prevent safe partition-local state publication. Validate both update
// and initialization shapes before treating them as internal bookkeeping.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutDecoder.h"

#include "V3DfgContext.h"

namespace V3RepCut {
namespace {

bool nativeDecoderStorage(const AstVarRef* refp) {
    if (!refp || !refp->varScopep()) return false;
    const AstVar* const varp = refp->varp();
    return varp->isInternal() && !varp->isPrimaryIO() && !varp->isSc()
           && !varp->isSigUserRdPublic() && !varp->isSigUserRWPublic();
}

bool decoderTable(const AstVarRef* refp) {
    if (!nativeDecoderStorage(refp)) return false;
    const AstUnpackArrayDType* const dtypep
        = VN_CAST(refp->dtypep()->skipRefp(), UnpackArrayDType);
    return dtypep && dtypep->subDTypep()->skipRefp()->isIntegralOrPacked()
           && dtypep->subDTypep()->width() == 1;
}

}  // namespace

bool isNativeDecoderUpdate(const AstAlways* nodep) {
    if (!nodep->isDfgDecoder() || nodep->keyword() != VAlwaysKwd::ALWAYS_COMB
        || nodep->isSuspendable() || nodep->needsVlProcess())
        return false;
    // Preserve the exact cache update contract: clear the previous slot, set
    // the current slot, then remember the current index. No HDL state is written.
    const AstAssign* const clearp = VN_CAST(nodep->stmtsp(), Assign);
    const AstAssign* const setp = clearp ? VN_CAST(clearp->nextp(), Assign) : nullptr;
    const AstAssign* const rememberp = setp ? VN_CAST(setp->nextp(), Assign) : nullptr;
    if (!rememberp || rememberp->nextp() || clearp->timingControlp() || setp->timingControlp()
        || rememberp->timingControlp())
        return false;
    const AstArraySel* const oldp = VN_CAST(clearp->lhsp(), ArraySel);
    const AstArraySel* const currentp = VN_CAST(setp->lhsp(), ArraySel);
    const AstConst* const zerop = VN_CAST(clearp->rhsp(), Const);
    const AstConst* const onep = VN_CAST(setp->rhsp(), Const);
    if (!oldp || !currentp || !zerop || !zerop->isZero() || !onep || !onep->isOne()) return false;
    const AstVarRef* const tablep = VN_CAST(oldp->fromp(), VarRef);
    const AstVarRef* const otherp = VN_CAST(currentp->fromp(), VarRef);
    const AstVarRef* const previousp = VN_CAST(oldp->bitp(), VarRef);
    const AstVarRef* const targetp = VN_CAST(rememberp->lhsp(), VarRef);
    if (!decoderTable(tablep) || !otherp || tablep->varScopep() != otherp->varScopep()
        || !nativeDecoderStorage(previousp) || !targetp
        || previousp->varScopep() != targetp->varScopep() || !previousp->varp()->ignoreSchedWrite()
        || !currentp->bitp()->sameTree(rememberp->rhsp()))
        return false;
    const int width = currentp->bitp()->width();
    const AstUnpackArrayDType* const dtypep
        = VN_AS(tablep->dtypep()->skipRefp(), UnpackArrayDType);
    return width >= 1 && width <= static_cast<int>(V3DfgBinToOneHotContext::WIDTH_MAX)
           && previousp->width() == width && dtypep->elementsConst() == (1 << width)
           && !currentp->bitp()->exists([](AstNode* childp) { return !childp->isPure(); });
}

bool isNativeDecoderInitialization(const AstInitialStatic* nodep) {
    if (!nodep->isDfgDecoder() || nodep->isSuspendable() || nodep->needsVlProcess()) return false;
    const AstAssign* const assignp = VN_CAST(nodep->stmtsp(), Assign);
    const AstStmtExpr* const stmtp = assignp ? VN_CAST(assignp->nextp(), StmtExpr) : nullptr;
    if (!stmtp || stmtp->nextp() || assignp->timingControlp()) return false;
    const AstVarRef* const previousp = VN_CAST(assignp->lhsp(), VarRef);
    const AstConst* const zerop = VN_CAST(assignp->rhsp(), Const);
    const AstCMethodHard* const fillp = VN_CAST(stmtp->exprp(), CMethodHard);
    if (!nativeDecoderStorage(previousp) || !previousp->varp()->ignoreSchedWrite() || !zerop
        || !zerop->isZero() || !fillp || fillp->method() != VCMethod::UNPACKED_FILL
        || fillp->withp() || fillp->usePtr())
        return false;
    const AstConst* const valuep = VN_CAST(fillp->pinsp(), Const);
    return decoderTable(VN_CAST(fillp->fromp(), VarRef)) && valuep && valuep->isZero()
           && !valuep->nextp();
}

}  // namespace V3RepCut
