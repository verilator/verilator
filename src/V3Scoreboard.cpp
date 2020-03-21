// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's element scoreboarding
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Scoreboard.h"

class ScoreboardTestElem {
public:
    // MEMBERS
    uint32_t m_score;
    uint32_t m_id;
    // CONSTRUCTORS
    explicit ScoreboardTestElem(uint32_t score) : m_score(score) {
        static uint32_t s_serial = 0;
        m_id = ++s_serial;
    }
    ScoreboardTestElem() {}
    // METHODS
    static uint32_t scoreFn(const ScoreboardTestElem* elp) { return elp->m_score; }

    bool operator< (const ScoreboardTestElem& other) const {
        return m_id < other.m_id;
    }
};

void V3ScoreboardBase::selfTest() {
    V3Scoreboard<ScoreboardTestElem, uint32_t> sb(ScoreboardTestElem::scoreFn, true);

    UASSERT(!sb.needsRescore(), "SelfTest: Empty sb should not need rescore.");

    ScoreboardTestElem e1(10);
    ScoreboardTestElem e2(20);
    ScoreboardTestElem e3(30);

    sb.addElem(&e1);
    sb.addElem(&e2);
    sb.addElem(&e3);

    UASSERT(sb.needsRescore(), "SelfTest: Newly filled sb should need a rescore.");
    UASSERT(sb.needsRescore(&e1),
            "SelfTest: Individual newly-added element should need rescore");
    UASSERT(NULL == sb.bestp(),
            "SelfTest: Newly filled sb should have nothing eligible for Bestp()");

    sb.rescore();

    UASSERT(!sb.needsRescore(), "SelfTest: Newly rescored sb should not need rescore");
    UASSERT(!sb.needsRescore(&e1),
            "SelfTest: Newly rescored sb should not need an element rescored");
    UASSERT(e2.m_score == sb.cachedScore(&e2),
            "SelfTest: Cached score should match current score");
    UASSERT(&e1 == sb.bestp(),
            "SelfTest: Should return element with lowest (best) score");

    // Change one element's score
    sb.hintScoreChanged(&e2);
    e2.m_score = 21;
    UASSERT(sb.needsRescore(&e2),
            "SelfTest: Should need rescore on elem after hintScoreChanged");

    // Remove an element
    UASSERT(sb.contains(&e1), "SelfTest: e1 should be there");
    sb.removeElem(&e1);
    UASSERT(!sb.contains(&e1), "SelfTest: e1 should be gone");
    UASSERT(sb.contains(&e2), "SelfTest: e2 should be there, despite needing rescore");

    // Now e3 should be our best-scoring element, even though
    // e2 has a better score, since e2 is pending rescore.
    UASSERT(&e3 == sb.bestp(), "SelfTest: Expect e3 as best element with known score.");
    sb.rescore();
    UASSERT(&e2 == sb.bestp(), "SelfTest: Expect e2 as best element again after Rescore");
}
