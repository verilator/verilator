// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Variable ordering
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
// V3VariableOrder's Transformations:
//
// Each module:
//   Order module variables
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3VariableOrder.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3EmitCBase.h"
#include "V3Global.h"
#include "V3TSP.h"

#include <algorithm>
#include <vector>

//######################################################################
// Establish mtask variable sort order in mtasks mode

class VarTspSorter final : public V3TSP::TspStateBase {
private:
    // MEMBERS
    const MTaskIdSet& m_mtaskIds;  // Mtask we're ordering
    static unsigned s_serialNext;  // Unique ID to establish serial order
    unsigned m_serial;  // Serial ordering
public:
    // CONSTRUCTORS
    explicit VarTspSorter(const MTaskIdSet& mtaskIds)
        : m_mtaskIds(mtaskIds) {  // Cannot be {} or GCC 4.8 false warning
        m_serial = ++s_serialNext;  // Cannot be ()/{} or GCC 4.8 false warning
    }
    ~VarTspSorter() override = default;
    // METHODS
    virtual bool operator<(const TspStateBase& other) const override {
        return operator<(static_cast<const VarTspSorter&>(other));
    }
    bool operator<(const VarTspSorter& other) const { return m_serial < other.m_serial; }
    const MTaskIdSet& mtaskIds() const { return m_mtaskIds; }
    virtual int cost(const TspStateBase* otherp) const override {
        return cost(static_cast<const VarTspSorter*>(otherp));
    }
    int cost(const VarTspSorter* otherp) const {
        int cost = diffs(m_mtaskIds, otherp->m_mtaskIds);
        cost += diffs(otherp->m_mtaskIds, m_mtaskIds);
        return cost;
    }
    // Returns the number of elements in set_a that don't appear in set_b
    static int diffs(const MTaskIdSet& set_a, const MTaskIdSet& set_b) {
        int diffs = 0;
        for (int i : set_a) {
            if (set_b.find(i) == set_b.end()) ++diffs;
        }
        return diffs;
    }
};

unsigned VarTspSorter::s_serialNext = 0;

class VariableOrder final {
    // NODE STATE
    //  AstVar::user1()    -> attributes, via m_attributes
    const VNUser1InUse m_user1InUse;  // AstVar

    struct VarAttributes {
        uint32_t stratum;  // Roughly equivalent to alignment requirement, to avoid padding
        bool anonOk;  // Can be emitted as part of anonymous structure
    };

    AstUser1Allocator<AstVar, VarAttributes> m_attributes;  // Attributes used for sorting

    //######################################################################

    // Simple sort
    void simpleSortVars(std::vector<AstVar*>& varps) {
        stable_sort(varps.begin(), varps.end(),
                    [this](const AstVar* ap, const AstVar* bp) -> bool {
                        if (ap->isStatic() != bp->isStatic()) {  // Non-statics before statics
                            return bp->isStatic();
                        }
                        const auto& attrA = m_attributes(ap);
                        const auto& attrB = m_attributes(bp);
                        if (attrA.anonOk != attrB.anonOk) {  // Anons before non-anons
                            return attrA.anonOk;
                        }
                        return attrA.stratum < attrB.stratum;  // Finally sort by stratum
                    });
    }

    // Sort by MTask-affinity first, then the same as simpleSortVars
    void tspSortVars(std::vector<AstVar*>& varps) {
        // Map from "MTask affinity" -> "variable list"
        std::map<const MTaskIdSet, std::vector<AstVar*>> m2v;
        for (AstVar* const varp : varps) { m2v[varp->mtaskIds()].push_back(varp); }

        // Create a TSP sort state for each unique MTaskIdSet, except for the empty set
        V3TSP::StateVec states;
        for (const auto& pair : m2v) {
            if (pair.first.empty()) continue;
            states.push_back(new VarTspSorter(pair.first));
        }

        // Do the TSP sort
        V3TSP::StateVec sortedStates;
        V3TSP::tspSort(states, &sortedStates);

        varps.clear();

        // Helper function to sort given vector, then append to 'varps'
        const auto sortAndAppend = [this, &varps](std::vector<AstVar*>& subVarps) {
            simpleSortVars(subVarps);
            for (AstVar* const varp : subVarps) { varps.push_back(varp); }
        };

        // Enumerate by sorted MTaskIdSet, sort within the set separately
        for (const V3TSP::TspStateBase* const stateBasep : sortedStates) {
            const VarTspSorter* const statep = dynamic_cast<const VarTspSorter*>(stateBasep);
            sortAndAppend(m2v[statep->mtaskIds()]);
            VL_DO_DANGLING(delete statep, statep);
        }

        // Finally add the variables with no known MTask affinity
        sortAndAppend(m2v[MTaskIdSet()]);
    }

    void orderModuleVars(AstNodeModule* modp) {
        std::vector<AstVar*> varps;

        // Unlink all module variables from the module, compute attributes
        for (AstNode *nodep = modp->stmtsp(), *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                // Unlink, add to vector
                varp->unlinkFrBack();
                varps.push_back(varp);
                // Compute attributes up front
                auto& attributes = m_attributes(varp);
                // Stratum
                const int sigbytes = varp->dtypeSkipRefp()->widthAlignBytes();
                attributes.stratum = (v3Global.opt.hierChild() && varp->isPrimaryIO()) ? 0
                                     : (varp->isUsedClock() && varp->widthMin() == 1)  ? 1
                                     : VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)  ? 9
                                     : (varp->basicp() && varp->basicp()->isOpaque())  ? 8
                                     : (varp->isScBv() || varp->isScBigUint())         ? 7
                                     : (sigbytes == 8)                                 ? 6
                                     : (sigbytes == 4)                                 ? 5
                                     : (sigbytes == 2)                                 ? 3
                                     : (sigbytes == 1)                                 ? 2
                                                                                       : 10;
                // Anonymous structure ok
                attributes.anonOk = EmitCBaseVisitor::isAnonOk(varp);
            }
        }

        if (!varps.empty()) {
            // Sort variables
            if (!v3Global.opt.mtasks()) {
                simpleSortVars(varps);
            } else {
                tspSortVars(varps);
            }

            // Insert them back under the module, in the new order, but at
            // the front of the list so they come out first in dumps/XML.
            auto it = varps.cbegin();
            AstVar* const firstp = *it++;
            for (; it != varps.cend(); ++it) firstp->addNext(*it);
            if (AstNode* const stmtsp = modp->stmtsp()) {
                stmtsp->unlinkFrBackWithNext();
                firstp->addNext(stmtsp);
            }
            modp->addStmtp(firstp);
        }
    }

public:
    static void processModule(AstNodeModule* modp) { VariableOrder().orderModuleVars(modp); }
};

//######################################################################
// V3VariableOrder static functions

void V3VariableOrder::orderAll() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        VariableOrder::processModule(modp);
    }
    V3Global::dumpCheckGlobalTree("variableorder", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
