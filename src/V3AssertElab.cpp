// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inline SVA property and sequence instances
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3AssertElab's Transformations:
//
//  Runs after V3Width and before V3WidthCommit.
//  - Lower a sequence used as an event control into a cover sequence firing
//    a synthesized event (IEEE 1800-2023 9.4.2.4), so its instance is
//    inlined like the others.
//  - Replace a property instance forming a whole property spec with the
//    property body (IEEE 1800-2023 16.12.1). Property-local variables
//    become module temporaries (IEEE 1800-2023 16.10).
//  - Replace a property instance nested in an expression with the expression
//    of the property body. A body with a disable condition, a clocking event
//    or a multi-cycle operator is reported instead.
//  - Replace each sequence instance with the sequence body
//    (IEEE 1800-2023 16.8).
//  Actual arguments are substituted for formal arguments (IEEE 1800-2023 F.4.1),
//  then the cycle delays of the body are checked.
//  Property and sequence declarations are kept, as V3Undriven lints the
//  variables they declare and read. V3AssertPre removes them.
//
//  A sequence or property instance anywhere but in the property expression of
//  an assertion is reported as illegal, as sequence event controls are already
//  lowered.
//  Instances in a restrict property are not inlined either, as V3AssertNfa
//  removes it.
//  Inlined bodies keep their declaration lines with coverage off, as
//  V3Coverage does not cover declarations.
//  The body of a property instance that is itself a property instance is
//  marked as an instance chain, which V3AssertNfa leaves to V3AssertPre.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertElab.h"

#include "V3Assert.h"
#include "V3LinkLValue.h"
#include "V3Stats.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

// Lower a sequence used as an event control ('@seq', IEEE 1800-2023 9.4.2.4) into a
// synthesized event fired by an internal 'cover sequence' on each end-of-match
class SeqEventLowerVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    V3UniqueNames m_names{"__VseqEvent"};  // Synthesized event names

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstSenItem* nodep) override {
        AstSchemaRef* const schemaRefp = VN_CAST(nodep->sensp(), SchemaRef);
        if (schemaRefp && VN_IS(schemaRefp->schemap(), Sequence)) {
            FileLine* const flp = nodep->fileline();
            AstVar* const eventp = new AstVar{flp, VVarType::MODULETEMP, m_names.get(nodep),
                                              m_modp->findBasicDType(VBasicDTypeKwd::EVENT)};
            eventp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(eventp);
            v3Global.setHasEvents();
            schemaRefp->unlinkFrBack();
            nodep->sensp(new AstVarRef{flp, eventp, VAccess::READ});
            const bool automaticActual = schemaRefp->exists(
                [](const AstNodeVarRef* refp) { return refp->varp()->lifetime().isAutomatic(); });
            if (automaticActual) {
                nodep->v3error("Arguments to a sequence used as an event control must be"
                               " static (IEEE 1800-2023 9.4.2.4)");
                VN_AS(schemaRefp->schemap(), Sequence)->isReferenced(false);
                VL_DO_DANGLING(pushDeletep(schemaRefp), schemaRefp);
                return;
            }
            AstFireEvent* const firep
                = new AstFireEvent{flp, new AstVarRef{flp, eventp, VAccess::WRITE}, false};
            AstCover* const coverp
                = new AstCover{flp, new AstPropSpec{flp, nullptr, nullptr, schemaRefp}, firep,
                               VAssertType::CONCURRENT};
            coverp->isCoverSeq(true);
            coverp->isSeqEvent(true);
            m_modp->addStmtsp(new AstAlways{flp, VAlwaysKwd::ASSERT_COVER, nullptr, coverp});
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit SeqEventLowerVisitor(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################

class AssertElabVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    // In the property expression of an assertion, the only place left where a sequence or
    // property instance is legal, as SeqEventLowerVisitor lowered the sequence event controls
    bool m_inPropExpr = false;
    V3UniqueNames m_propVarNames{"__Vpropvar"};  // Property-local variable names
    // Declaration file line -> its copy with coverage off, for inlined bodies
    std::unordered_map<FileLine*, FileLine*> m_noCoverFileLines;
    VDouble0 m_statPropInlined;  // Statistic tracking
    VDouble0 m_statSeqInlined;  // Statistic tracking

    // METHODS
    // The property instantiated as the whole of specp, if any
    static const AstProperty* instancedProperty(const AstPropSpec* specp) {
        const AstSchemaRef* const schemaRefp = VN_CAST(specp->propp(), SchemaRef);
        return schemaRefp ? VN_CAST(schemaRefp->schemap(), Property) : nullptr;
    }
    // Copy of a declaration file line with coverage off, shared by all inlined copies
    FileLine* noCoverFileLine(FileLine* flp) {
        FileLine*& copyp = m_noCoverFileLines[flp];
        if (!copyp) {
            copyp = new FileLine{flp};
            copyp->coverageOn(false);
        }
        return copyp;
    }
    // Turn coverage off on the file lines of a subtree.
    void coverageOff(AstNode* nodep) {
        nodep->foreach([&](AstNode* np) { np->fileline(noCoverFileLine(np->fileline())); });
    }
    // Check the cycle delays of a sequence or property instance, after its formal arguments are
    // replaced with the actual arguments (IEEE 1800-2023 16.8), reporting errors on instp
    static void checkInstanceDelays(AstNode* nodep, AstNode* instp) {
        // Collect first, as checking edits the delays
        std::vector<AstDelay*> delayps;
        nodep->foreach([&](AstDelay* delayp) { delayps.push_back(delayp); });
        for (AstDelay* const delayp : delayps) V3AssertCommon::checkSvaCycleDelay(delayp, instp);
    }
    // Replace formal argument references under bodyp with the actual arguments of schemaRefp,
    // and retarget property-local variable references per localVarMap
    void substituteArgs(AstNode* bodyp, AstSchemaRef* schemaRefp,
                        const std::unordered_map<const AstVar*, AstVar*>& localVarMap) {
        const V3TaskConnects tconnects = V3Task::taskConnects(schemaRefp);
        std::unordered_map<const AstVar*, AstNodeExpr*> portMap;
        for (const auto& tconnect : tconnects) {
            portMap[tconnect.first] = tconnect.second->exprp();
        }
        bodyp->foreach([&](AstVarRef* refp) {
            const auto portIt = portMap.find(refp->varp());
            if (portIt != portMap.end()) {
                AstNodeExpr* const actualp = portIt->second->cloneTree(false);
                // An assigned formal makes the actual an lvalue
                if (refp->access().isWriteOrRW()) {
                    V3LinkLValue::linkLValueSet(actualp, refp->access());
                }
                refp->replaceWith(actualp);
                VL_DO_DANGLING(pushDeletep(refp), refp);
                return;
            }
            const auto localIt = localVarMap.find(refp->varp());
            if (localIt != localVarMap.end()) refp->varp(localIt->second);
        });
        // Cycle delays with a formal argument are checked once it is substituted
        checkInstanceDelays(bodyp, schemaRefp);
    }
    // Clone the body of a property instance, with the actual arguments substituted
    AstPropSpec* cloneProperty(AstSchemaRef* schemaRefp, const AstProperty* propp) {
        AstPropSpec* const specp = propp->specp()->cloneTree(false);
        coverageOff(specp);
        // Promote property-local variables to module-level temps (IEEE 1800-2023 16.10)
        std::unordered_map<const AstVar*, AstVar*> localVarMap;
        for (AstNode* const declp : propp->declspList()) {
            AstVar* const varp = VN_AS(declp, Var);
            if (!varp->isIO()) {
                // V3Undriven checks the declared variable, not its per-instance copies
                FileLine* const flp = new FileLine{noCoverFileLine(varp->fileline())};
                flp->modifyWarnOff(V3ErrorCode::UNDRIVEN, true);
                flp->modifyWarnOff(V3ErrorCode::UNUSEDSIGNAL, true);
                AstVar* const newVarp = new AstVar{flp, VVarType::MODULETEMP,
                                                   m_propVarNames.get(varp), varp->dtypep()};
                newVarp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(newVarp);
                localVarMap[varp] = newVarp;
            }
        }
        substituteArgs(specp, schemaRefp, localVarMap);
        ++m_statPropInlined;
        return specp;
    }
    void inlineProperty(AstPropSpec* outerSpecp, AstSchemaRef* schemaRefp,
                        const AstProperty* propp) {
        AstPropSpec* const propSpecp = cloneProperty(schemaRefp, propp);
        if (outerSpecp->fromInstanceChain() || instancedProperty(propSpecp)) {
            propSpecp->fromInstanceChain(true);
        }

        // Merge disable iff (IEEE 1800-2023 16.12.1)
        if (outerSpecp->disablep() && propSpecp->disablep()) {
            outerSpecp->v3error("disable iff expression before property call "
                                "and in its body is not legal");
            pushDeletep(propSpecp->disablep()->unlinkFrBack());
        }
        if (outerSpecp->disablep()) propSpecp->disablep(outerSpecp->disablep()->unlinkFrBack());

        if (outerSpecp->sensesp() && propSpecp->sensesp()) {
            outerSpecp->v3warn(E_UNSUPPORTED,
                               "Unsupported: Clock event before property call and in its body");
            pushDeletep(propSpecp->sensesp()->unlinkFrBack());
        }
        if (outerSpecp->sensesp()) propSpecp->sensesp(outerSpecp->sensesp()->unlinkFrBack());

        outerSpecp->replaceWith(propSpecp);
        VL_DO_DANGLING(pushDeletep(outerSpecp), outerSpecp);
    }
    void inlineNestedProperty(AstSchemaRef* schemaRefp, const AstProperty* propp) {
        AstPropSpec* const specp = cloneProperty(schemaRefp, propp);
        AstNode* replp = nullptr;
        if (specp->disablep()) {
            schemaRefp->v3error("Illegal 'disable iff' in a nested property instance"
                                " (IEEE 1800-2023 16.12.1)");
        } else if (specp->sensesp()) {
            schemaRefp->v3warn(E_UNSUPPORTED,
                               "Unsupported: clock event in a nested property instance");
        } else if (specp->propp()->exists(
                       [](const AstNodeExpr* np) { return np->isMultiCycleSva(); })) {
            schemaRefp->v3warn(E_UNSUPPORTED,
                               "Unsupported: multi-cycle body in a nested property instance");
        } else {
            // The instance a chain resolves to is checked next, report it at this instance
            if (instancedProperty(specp)) specp->propp()->fileline(schemaRefp->fileline());
            replp = specp->propp()->unlinkFrBack();
        }
        if (!replp) replp = new AstConst{schemaRefp->fileline(), AstConst::BitFalse{}};
        schemaRefp->replaceWith(replp);
        VL_DO_DANGLING(pushDeletep(schemaRefp), schemaRefp);
        VL_DO_DANGLING(pushDeletep(specp), specp);
    }
    void inlineSequence(AstSchemaRef* schemaRefp, AstSequence* seqp) {
        // Clone the body expression since the sequence may be referenced multiple times
        AstNodeExpr* const clonedp = seqp->exprp()->cloneTree(false);
        coverageOff(clonedp);
        substituteArgs(clonedp, schemaRefp, {});
        schemaRefp->replaceWith(clonedp);
        VL_DO_DANGLING(pushDeletep(schemaRefp), schemaRefp);
        // V3AssertPre reports sequences still referenced after inlining as unsupported
        seqp->isReferenced(false);
        ++m_statSeqInlined;
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER_COPY(m_propVarNames);
        m_modp = nodep;
        m_propVarNames.reset();
        iterateChildren(nodep);
    }
    void visit(AstPropSpec* nodep) override {
        if (AstSchemaRef* const schemaRefp = VN_CAST(nodep->propp(), SchemaRef)) {
            if (const AstProperty* const propp = VN_CAST(schemaRefp->schemap(), Property)) {
                // The replacement is iterated next, which inlines a property instance in its body
                inlineProperty(nodep, schemaRefp, propp);
                return;
            }
        }
        iterateAndNextNull(nodep->sensesp());
        iterateAndNextNull(nodep->disablep());
        VL_RESTORER(m_inPropExpr);
        m_inPropExpr = true;
        iterateAndNextNull(nodep->propp());
    }
    void visit(AstSenItem* nodep) override {
        // A clocking event inside a property expression has an expression condition
        VL_RESTORER(m_inPropExpr);
        m_inPropExpr = false;
        iterateChildren(nodep);
    }
    void visit(AstSchemaRef* nodep) override {
        AstSequence* const seqp = VN_CAST(nodep->schemap(), Sequence);
        if (!m_inPropExpr) {
            // A sequence or property instance is not an expression (IEEE 1800-2023 16.8, 16.12)
            nodep->v3error("Illegal use of "
                           << (seqp ? "sequence" : "property") << " instance "
                           << nodep->prettyNameQ() << " as an expression"
                           << (seqp ? " (IEEE 1800-2023 16.8)" : " (IEEE 1800-2023 16.12)"));
            return;
        }
        // The replacement is iterated next, which inlines the instances in its body
        if (seqp) {
            inlineSequence(nodep, seqp);
            return;
        }
        // V3LinkResolve substituted every let, so this is a property instance
        inlineNestedProperty(nodep, VN_AS(nodep->schemap(), Property));
    }
    // Declarations are inlined at their instances
    void visit(AstProperty*) override {}
    void visit(AstSequence*) override {}
    // A restrict property is not checked in simulation (IEEE 1800-2023 16.14.4)
    void visit(AstRestrict*) override {}
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertElabVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~AssertElabVisitor() override {
        V3Stats::addStat("Assertions, inlined property instances", m_statPropInlined);
        V3Stats::addStat("Assertions, inlined sequence instances", m_statSeqInlined);
    }
};

//######################################################################
// Top AssertElab class

void V3AssertElab::assertElabAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { SeqEventLowerVisitor{nodep}; }
    { AssertElabVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assertelab", 0, dumpTreeEitherLevel() >= 3);
}
