// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Test guarded RepCut optimizations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Exercise copy elimination, state release, local expression substitution, and
// selection preparation using synthetic ASTs with explicit lifetime cleanup.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3DfgPasses.h"
#include "V3RepCutOptimize.h"

#include <memory>

void V3RepCut::selfTestLocalExpressions(AstScope& scope) {
    FileLine* const flp = scope.fileline();
    std::vector<AstVarScope*> variables;
    const auto makeVar = [&](int width, VSigning sign = VSigning::UNSIGNED) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            "__Vrepcut_expression_test" + cvtToStr(variables.size()),
            scope.findBitDType(width, width, sign));
        vscp->varp()->isInternal(true);
        variables.push_back(vscp);
        return vscp;
    };
    const auto read = [&](AstVarScope* vscp) { return new AstVarRef{flp, vscp, VAccess::READ}; };
    const auto assign = [&](AstVarScope* dstp, AstNodeExpr* rhsp) {
        return new AstAssign{flp, new AstVarRef{flp, dstp, VAccess::WRITE}, rhsp};
    };
    AstVarScope* const enablep = makeVar(1);
    for (const int width : {7, 95}) {
        const VSigning sign = width == 95 ? VSigning::SIGNED : VSigning::UNSIGNED;
        AstVarScope* const ap = makeVar(width, sign);
        AstVarScope* const bp = makeVar(width, sign);
        AstVarScope* const tp = makeVar(width, sign);
        AstVarScope* const up = makeVar(width, sign);
        AstVarScope* const outp = makeVar(width, sign);
        std::vector<AstNodeStmt*> statements;
        const auto sum = [&]() { return new AstAdd{flp, read(ap), read(bp)}; };
        const auto check = [&](size_t expected, size_t limit = 32, bool keepTemp = false) {
            std::set<AstVarScope*> preserve{outp};
            if (keepTemp) preserve.insert(tp);
            UASSERT(substituteLocalExpressions(statements, preserve, limit) == expected,
                    "RepCut local expression availability or size proof");
            VNDeleter deleter;
            for (AstNodeStmt* const stmtp : statements) deleter.pushDeletep(stmtp);
            statements.clear();
        };
        statements = {assign(tp, sum()), assign(outp, read(tp))};
        check(1);
        statements = {assign(tp, sum()), assign(up, new AstXor{flp, read(tp), read(bp)}),
                      assign(outp, read(up))};
        check(2);
        statements = {assign(tp, sum()), assign(outp, read(tp))};
        check(0, 2);
        statements = {assign(tp, sum()), assign(outp, read(tp))};
        check(0, 32, true);
        // Direct state publication changes the value an earlier RHS captured.
        statements = {assign(tp, sum()), assign(ap, read(bp)), assign(outp, read(tp))};
        check(0);
        // The same source write in the consuming statement follows its RHS read.
        statements = {assign(tp, sum()), assign(ap, read(tp))};
        check(1);
        statements = {assign(tp, sum()), assign(outp, new AstXor{flp, read(tp), read(tp)})};
        check(0);
        statements = {assign(outp, read(tp)), assign(tp, sum())};
        check(0);
        statements = {assign(tp, sum()), assign(tp, read(bp)), assign(outp, read(tp))};
        check(0);
        statements = {assign(tp, sum()), new AstIf{flp, read(enablep), assign(outp, read(tp))}};
        check(0);
        statements = {new AstIf{flp, read(enablep), assign(tp, sum())},
                      new AstIf{flp, read(enablep), assign(outp, read(tp))}};
        check(0);
        AstAssign* const defp = assign(tp, sum());
        defp->addNext(assign(outp, read(tp)));
        statements = {new AstIf{flp, read(enablep), defp}};
        check(1);
        statements = {assign(tp, sum()), new AstCStmt{flp, "/* opaque barrier */"},
                      assign(outp, read(tp))};
        check(0);
        AstVarScope* const narrowp = makeVar(width - 1, sign);
        statements = {assign(narrowp, sum()), assign(outp, read(narrowp))};
        check(0);
    }
    VNDeleter deleter;
    for (AstVarScope* const vscp : variables) {
        AstVar* const varp = vscp->varp();
        deleter.pushDeletep(vscp->unlinkFrBack());
        deleter.pushDeletep(varp->unlinkFrBack());
    }
}

void V3RepCut::selfTestStateRelease(AstScope& scope) {
    FileLine* const flp = scope.fileline();
    std::vector<AstVarScope*> variables;
    const auto makeVar = [&](int width) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            "__Vrepcut_state_test" + cvtToStr(variables.size()),
            scope.findBitDType(width, width, VSigning::UNSIGNED));
        vscp->varp()->isInternal(true);
        variables.push_back(vscp);
        return vscp;
    };
    AstVarScope* const statep = makeVar(7);
    AstVarScope* const candidatep = makeVar(7);
    AstVarScope* const inputp = makeVar(7);
    AstVarScope* const outputp = makeVar(7);
    AstVarScope* const enablep = makeVar(1);
    AstVarScope* const widep = makeVar(95);
    AstVarScope* const wideCandidatep = makeVar(95);
    const auto read = [&](AstVarScope* vscp) { return new AstVarRef{flp, vscp, VAccess::READ}; };
    const auto assign = [&](AstVarScope* dstp, AstNodeExpr* rhsp) {
        return new AstAssign{flp, new AstVarRef{flp, dstp, VAccess::WRITE}, rhsp};
    };
    std::vector<AstNodeStmt*> statements;
    const auto clear = [&]() {
        VNDeleter deleter;
        for (AstNodeStmt* const stmtp : statements) deleter.pushDeletep(stmtp);
        statements.clear();
    };
    const std::map<AstVarScope*, AstVarScope*> destinations{{candidatep, statep}};
    const auto lhs = [](AstNodeStmt* stmtp) {
        return VN_AS(VN_AS(stmtp, Assign)->lhsp(), VarRef)->varScopep();
    };
    statements = {assign(candidatep, new AstAdd{flp, read(statep), read(inputp)})};
    UASSERT(releaseStateCandidates(statements, destinations) == std::set<AstVarScope*>{candidatep}
                && lhs(statements[0]) == statep,
            "RepCut missed a final old-state RHS read");
    clear();
    statements = {assign(candidatep, read(inputp)),
                  new AstIf{flp, read(enablep), assign(outputp, read(statep))}};
    UASSERT(releaseStateCandidates(statements, destinations).empty(),
            "RepCut published state before a later guarded read");
    clear();
    statements = {assign(candidatep, read(inputp)),
                  new AstIf{flp, new AstRedOr{flp, read(statep)}, assign(outputp, read(inputp))}};
    UASSERT(releaseStateCandidates(statements, destinations).empty(),
            "RepCut published state before a later predicate read");
    clear();
    statements = {assign(outputp, read(statep)), assign(candidatep, read(inputp))};
    UASSERT(releaseStateCandidates(statements, destinations).size() == 1,
            "RepCut missed a captured earlier state read");
    UASSERT(eliminateCopies(statements, {statep, outputp}) == 0 && statements.size() == 2,
            "RepCut lost an old-state snapshot after direct publication");
    clear();
    statements = {assign(candidatep, read(inputp)), assign(outputp, read(candidatep))};
    UASSERT(releaseStateCandidates(statements, destinations).empty(),
            "RepCut released a candidate still read by evaluation");
    clear();
    statements = {assign(statep, read(inputp)), assign(candidatep, read(inputp))};
    UASSERT(releaseStateCandidates(statements, destinations).empty(),
            "RepCut released a candidate with an existing state writer");
    clear();
    statements = {assign(candidatep, read(inputp)), assign(candidatep, read(statep))};
    UASSERT(releaseStateCandidates(statements, destinations).empty(),
            "RepCut released a multiply-written candidate");
    clear();
    statements = {assign(wideCandidatep, read(widep))};
    UASSERT(releaseStateCandidates(statements, {{wideCandidatep, widep}}).size() == 1
                && lhs(statements[0]) == widep,
            "RepCut failed to release a wide state candidate");
    clear();
    // A guarded write can retain its old-state hold without a private buffer.
    AstAssign* const guardedp = assign(candidatep, read(inputp));
    statements = {assign(candidatep, read(statep)), new AstIf{flp, read(enablep), guardedp}};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).size() == 1
                && lhs(statements[0]) == statep && lhs(guardedp) == statep,
            "RepCut failed to release a guarded state candidate");
    clear();
    statements = {new AstIf{flp, read(enablep), assign(candidatep, read(inputp))},
                  assign(outputp, read(statep))};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).empty(),
            "RepCut released state before a later unguarded read");
    clear();
    statements = {new AstIf{flp, read(enablep), assign(candidatep, read(inputp))},
                  new AstIf{flp, new AstRedOr{flp, read(statep)}, assign(outputp, read(inputp))}};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).empty(),
            "RepCut released state before a later predicate read");
    clear();
    AstAssign* const snapshotp = assign(outputp, read(statep));
    AstAssign* const finalp = assign(candidatep, read(inputp));
    snapshotp->addNext(finalp);
    statements = {new AstIf{flp, read(enablep), snapshotp}};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).size() == 1
                && lhs(finalp) == statep,
            "RepCut missed a last read inside a guard");
    clear();
    statements = {assign(candidatep, read(inputp)), assign(candidatep, read(statep))};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).empty(),
            "RepCut changed an old-state restoration after an earlier candidate write");
    clear();
    statements = {assign(candidatep, read(statep)), assign(candidatep, read(inputp)),
                  new AstIf{flp, read(enablep), assign(candidatep, read(inputp))}};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).size() == 1,
            "RepCut failed to preserve multiple writes after all old-state reads");
    clear();
    statements = {assign(candidatep, read(inputp)), assign(outputp, read(candidatep))};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).empty(),
            "RepCut released a candidate with an internal reader");
    clear();
    statements = {assign(statep, read(inputp)), assign(candidatep, read(inputp))};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).empty(),
            "RepCut released an already-written destination");
    clear();
    statements = {assign(candidatep, read(inputp)), new AstCStmt{flp, "/* observer */"}};
    UASSERT(releaseGuardedStateCandidates(statements, destinations).empty(),
            "RepCut released state across an opaque observer");
    clear();
    statements = {new AstIf{flp, read(enablep), assign(wideCandidatep, read(widep))}};
    UASSERT(releaseGuardedStateCandidates(statements, {{wideCandidatep, widep}}).size() == 1,
            "RepCut failed to release a guarded wide state candidate");
    clear();
    VNDeleter deleter;
    for (AstVarScope* const vscp : variables) {
        AstVar* const varp = vscp->varp();
        deleter.pushDeletep(vscp->unlinkFrBack());
        deleter.pushDeletep(varp->unlinkFrBack());
    }
}

void V3RepCut::selfTestCopies(AstScope& scope) {
    FileLine* const flp = scope.fileline();
    std::vector<AstVarScope*> variables;
    const auto makeVar = [&](int width, VSigning sign = VSigning::UNSIGNED) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            "__Vrepcut_copy_test" + cvtToStr(variables.size()),
            scope.findBitDType(width, width, sign));
        vscp->varp()->isInternal(true);
        vscp->varp()->noReset(true);
        variables.push_back(vscp);
        return vscp;
    };
    AstVarScope* const inputp = makeVar(7);
    AstVarScope* const ap = makeVar(7);
    AstVarScope* const bp = makeVar(7);
    AstVarScope* const outputp = makeVar(7);
    AstVarScope* const enablep = makeVar(1);
    AstVarScope* const decisionp = makeVar(1);
    AstVarScope* const signedp = makeVar(7, VSigning::SIGNED);
    const auto read = [&](AstVarScope* vscp) { return new AstVarRef{flp, vscp, VAccess::READ}; };
    const auto assign = [&](AstVarScope* dstp, AstNodeExpr* rhsp) {
        return new AstAssign{flp, new AstVarRef{flp, dstp, VAccess::WRITE}, rhsp};
    };
    std::vector<AstNodeStmt*> statements;
    const auto clear = [&]() {
        VNDeleter deleter;
        for (AstNodeStmt* const stmtp : statements) deleter.pushDeletep(stmtp);
        statements.clear();
    };
    const auto sourceOf
        = [](const AstAssign* nodep) { return VN_AS(nodep->rhsp(), VarRef)->varScopep(); };
    // The copied value is immutable across separately emitted guard segments.
    AstAssign* outp = assign(outputp, read(bp));
    AstIf* const guardedp = new AstIf{flp, read(enablep), outp};
    statements = {assign(ap, read(inputp)), new AstIf{flp, read(enablep), assign(bp, read(ap))},
                  guardedp};
    UASSERT(eliminateCopies(statements, {outputp}) == 2 && statements.size() == 1
                && statements[0] == guardedp && sourceOf(outp) == inputp,
            "RepCut copies did not preserve the guarded snapshot");
    clear();
    // A skipped definition cannot supply an unguarded read of an old value.
    outp = assign(outputp, read(ap));
    statements = {new AstIf{flp, read(enablep), assign(ap, read(inputp))}, outp};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && sourceOf(outp) == ap,
            "RepCut used a copy outside its defining guard");
    clear();
    // A source changed after a copy must not change the captured value.
    outp = assign(outputp, read(bp));
    statements = {assign(ap, read(inputp)), assign(bp, read(ap)),
                  assign(ap, new AstConst{flp, AstConst::WidthedValue{}, 7, 0x55}), outp};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && sourceOf(outp) == bp,
            "RepCut propagated a multiply-written source");
    clear();
    // Repeating a test after modifying its condition is not the same guard.
    outp = assign(outputp, read(ap));
    statements = {new AstIf{flp, read(enablep), assign(ap, read(inputp))},
                  assign(enablep, new AstConst{flp, AstConst::BitTrue{}}),
                  new AstIf{flp, read(enablep), outp}};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && sourceOf(outp) == ap,
            "RepCut conflated guards with a changing predicate");
    clear();
    // Even one write is unsafe when it happens after the snapshot.
    outp = assign(outputp, read(bp));
    statements = {assign(bp, read(ap)), assign(ap, read(inputp)), outp};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && sourceOf(outp) == bp,
            "RepCut propagated a future definition");
    clear();
    // An earlier read observes the previous invocation's value.
    outp = assign(outputp, read(ap));
    statements = {outp, assign(ap, read(inputp))};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && sourceOf(outp) == ap,
            "RepCut changed a read before its definition");
    clear();
    // Signedness changes are not identity copies.
    outp = assign(outputp, read(signedp));
    statements = {assign(signedp, read(inputp)), outp};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && sourceOf(outp) == signedp,
            "RepCut removed a type-changing copy");
    clear();
    AstIf* const branchp = new AstIf{flp, read(decisionp), assign(outputp, read(inputp))};
    statements = {assign(decisionp, new AstRedOr{flp, read(enablep)}), branchp};
    UASSERT(eliminateCopies(statements, {outputp}) == 1 && statements.size() == 1
                && VN_AS(branchp->condp(), VarRef)->varScopep() == enablep,
            "RepCut did not propagate a one-bit decision");
    clear();
    // Snapshot candidates retain their own storage even when they are copies.
    outp = assign(outputp, read(inputp));
    statements = {outp};
    UASSERT(eliminateCopies(statements, {outputp}) == 0 && statements[0] == outp,
            "RepCut eliminated an externally published snapshot");
    clear();
    // A private intermediate stays local; a value read under a later guard is
    // a block output, and publication remains live without an AST read here.
    statements = {assign(ap, new AstXor{flp, read(inputp),
                                        new AstConst{flp, AstConst::WidthedValue{}, 7, 0x35}}),
                  assign(bp, new AstAdd{flp, read(ap), read(ap)}),
                  new AstIf{flp, read(enablep), assign(outputp, read(bp))}};
    std::vector<std::set<AstVarScope*>> liveOuts = blockLiveOuts(statements, {outputp});
    UASSERT(liveOuts.size() == 2 && liveOuts[0] == std::set<AstVarScope*>{bp}
                && liveOuts[1] == std::set<AstVarScope*>{outputp},
            "RepCut liveness lost a cross-block or publication value");
    clear();
    statements = {assign(decisionp, read(enablep)),
                  new AstIf{flp, read(decisionp), assign(outputp, read(inputp))}};
    liveOuts = blockLiveOuts(statements, {outputp});
    UASSERT(liveOuts.size() == 2 && liveOuts[0] == std::set<AstVarScope*>{decisionp},
            "RepCut liveness omitted a guard read");
    clear();
    // Separate writers must not independently delete a shared variable binding.
    statements
        = {assign(ap, read(inputp)), new AstIf{flp, read(enablep), assign(ap, read(inputp))}};
    liveOuts = blockLiveOuts(statements, {});
    UASSERT(liveOuts.size() == 2 && liveOuts[0] == std::set<AstVarScope*>{ap}
                && liveOuts[1] == std::set<AstVarScope*>{ap},
            "RepCut liveness omitted an external writer");
    clear();
    VNDeleter deleter;
    for (AstVarScope* const vscp : variables) {
        AstVar* const varp = vscp->varp();
        deleter.pushDeletep(vscp->unlinkFrBack());
        deleter.pushDeletep(varp->unlinkFrBack());
    }
}

void V3RepCut::selfTestSelections(AstScope& scope) {
    FileLine* const flp = scope.fileline();
    V3DfgContext ctx{"__VrepcutSelfTestSelections"};
    std::vector<AstVarScope*> variables;
    const auto makeVar = [&](int width, VSigning sign = VSigning::UNSIGNED) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            "__Vrepcut_selection_test" + cvtToStr(variables.size()),
            scope.findBitDType(width, width, sign));
        vscp->varp()->isInternal(true);
        variables.push_back(vscp);
        return vscp;
    };
    const auto read = [&](AstVarScope* vscp) { return new AstVarRef{flp, vscp, VAccess::READ}; };
    const auto assign = [&](AstVarScope* dstp, AstNodeExpr* rhsp) {
        return new AstAssign{flp, new AstVarRef{flp, dstp, VAccess::WRITE}, rhsp};
    };
    AstVarScope* const enablep = makeVar(1);
    std::vector<AstNodeStmt*> statements;
    const auto clear = [&]() {
        VNDeleter deleter;
        for (AstNodeStmt* const stmtp : statements) deleter.pushDeletep(stmtp);
        statements.clear();
    };
    const auto prepare = [&](const std::set<AstVarScope*>& inputs, size_t expected) {
        const auto countSelections = [&]() {
            size_t count = 0;
            for (AstNodeStmt* const stmtp : statements)
                stmtp->foreach([&](const AstCond*) { ++count; });
            return count;
        };
        const size_t before = countSelections();
        const std::vector<DfgBlock> blocks = prepareDfg(statements, inputs, {});
        UASSERT(countSelections() == before + expected, "RepCut selection availability proof");
        UASSERT(blocks.size() == blockLiveOuts(statements, {}).size(),
                "RepCut selection block enumeration");
        std::vector<std::set<AstVarScope*>> available;
        for (const DfgBlock& block : blocks) available.push_back(block.m_availableInputs);
        return available;
    };
    const auto representable = [&](const std::set<AstVarScope*>& inputs) {
        const VNUser1InUse user1InUse;
        bool result;
        {
            const std::unique_ptr<DfgGraph> dfgp
                = V3DfgPasses::astBlockToDfg(scope, statements, {}, inputs, ctx);
            result = static_cast<bool>(dfgp);
            if (dfgp) V3DfgPasses::typeCheck(*dfgp);
        }
        DfgDataType::reset();
        return result;
    };
    // The same proof must preserve non-word-aligned, wide and signed selections.
    for (const int width : {7, 95}) {
        const VSigning sign = width == 95 ? VSigning::SIGNED : VSigning::UNSIGNED;
        AstVarScope* const inputp = makeVar(width, sign);
        AstVarScope* const ap = makeVar(width, sign);
        AstVarScope* const bp = makeVar(width, sign);
        AstVarScope* const outputp = makeVar(width, sign);
        const auto select = [&](AstVarScope* dstp, AstNodeExpr* thenp, AstNodeExpr* elsep) {
            return new AstIf{flp, read(enablep), assign(dstp, thenp), assign(dstp, elsep)};
        };
        statements = {select(outputp, read(inputp), read(bp))};
        std::vector<std::set<AstVarScope*>> inputs = prepare({inputp, bp}, 1);
        UASSERT(inputs.size() == 1 && inputs[0] == (std::set<AstVarScope*>{inputp, bp})
                    && representable(inputs[0]) && !representable({}),
                "RepCut DFG admitted a selection without available inputs");
        clear();
        // A definition earlier in this block needs no external availability claim.
        statements = {assign(ap, new AstAdd{flp, read(inputp), read(bp)}),
                      select(outputp, read(ap), read(bp))};
        inputs = prepare({inputp, bp}, 1);
        UASSERT(inputs[0] == std::set<AstVarScope*>{bp} && representable(inputs[0]),
                "RepCut DFG lost an earlier local definition");
        clear();
        // A skipped definition must not expose stale storage, even under a
        // separately repeated test whose predicate might have changed.
        statements = {new AstIf{flp, read(enablep), assign(ap, read(inputp))},
                      assign(enablep, new AstConst{flp, AstConst::BitTrue{}}),
                      select(outputp, read(ap), read(bp))};
        prepare({inputp, bp, enablep}, 0);
        clear();
        // Lexically dominated uses are available, but an outside use is not.
        AstAssign* const definitionp = assign(ap, read(inputp));
        AstNode::addNext(static_cast<AstNodeStmt*>(definitionp),
                         select(outputp, read(ap), read(bp)));
        statements
            = {new AstIf{flp, read(enablep), definitionp}, select(outputp, read(ap), read(bp))};
        prepare({inputp, bp}, 1);
        UASSERT(VN_IS(statements.back(), If), "RepCut leaked a branch definition");
        clear();
        // A value defined by both paths is available after the join. The
        // computations themselves must stay in the original branch bodies.
        statements = {select(ap, new AstAdd{flp, read(inputp), read(bp)},
                             new AstSub{flp, read(inputp), read(bp)}),
                      select(outputp, read(ap), read(bp))};
        inputs = prepare({inputp, bp}, 1);
        UASSERT(VN_IS(statements.front(), If) && inputs.back().count(ap),
                "RepCut speculated guarded computation or lost join availability");
        clear();
        // A phase boundary is usable only with an explicit initialized-input proof.
        statements = {select(outputp, read(ap), read(bp))};
        prepare({bp}, 0);
        prepare({ap, bp}, 1);
        clear();
        // An input snapshot cannot be substituted with its later new value.
        statements = {select(outputp, read(ap), read(inputp)), assign(ap, read(inputp))};
        inputs = prepare({ap, inputp}, 1);
        UASSERT(!representable(inputs[0]), "RepCut DFG conflated old and new values");
        clear();
        statements = {assign(ap, read(inputp)), select(outputp, read(ap), read(bp)),
                      assign(ap, read(bp))};
        inputs = prepare({inputp, bp}, 1);
        UASSERT(!representable(inputs[0]), "RepCut DFG admitted repeated writers");
        clear();
        // The converter independently rejects computations in a Cond arm.
        AstCond* const condp
            = new AstCond{flp, read(enablep), new AstAdd{flp, read(inputp), read(bp)}, read(bp)};
        condp->dtypep(outputp->dtypep());
        statements = {assign(outputp, condp)};
        UASSERT(!representable({inputp, bp}), "RepCut DFG speculated a Cond arm");
        clear();
    }
    VNDeleter deleter;
    for (AstVarScope* const vscp : variables) {
        AstVar* const varp = vscp->varp();
        deleter.pushDeletep(vscp->unlinkFrBack());
        deleter.pushDeletep(varp->unlinkFrBack());
    }
}
