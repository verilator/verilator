// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementation of Christofides' algorithm to
//              approximate the solution to the traveling salesman problem.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3TSP_H_
#define _V3TSP_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

namespace V3TSP {
    // Perform a "Traveling Salesman Problem" optimizing sort
    // on any type you like -- so long as inherits from TspStateBase.

    class TspStateBase {
    public:
        // This is the cost function that the TSP sort will minimize.
        // All costs in V3TSP are int, chosen to match the type of
        // V3GraphEdge::weight() which will reflect each edge's cost.
        virtual int cost(const TspStateBase* otherp) const = 0;

        // This operator< must place a meaningless, arbitrary, but
        // stable order on all TspStateBase's. It's used only to
        // key maps so that iteration is stable, without relying
        // on pointer values that could lead to nondeterminism.
        virtual bool operator<(const TspStateBase& otherp) const = 0;
    };

    typedef std::vector<const TspStateBase*> StateVec;

    // Given an unsorted set of TspState's, sort them to minimize
    // the transition cost for walking the sorted list.
    void tspSort(const StateVec& states, StateVec* resultp);

    void selfTest();
}


#endif  // Guard
