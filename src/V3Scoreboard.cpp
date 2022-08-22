// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's element scoreboarding
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Scoreboard.h"

class ScoreboardTestElem;

struct Key {
    // Node: Structure layout chosen to minimize padding in PairingHeao<*>::Node
    uint64_t m_id;  // Unique ID part of edge score
    uint32_t m_score;  // Score part of ID
    bool operator<(const Key& other) const {
        // First by Score then by ID, but notice that we want minimums using a max-heap, so reverse
        return m_score > other.m_score || (m_score == other.m_score && m_id > other.m_id);
    }
};

using Scoreboard = V3Scoreboard<ScoreboardTestElem, Key>;

class ScoreboardTestElem final : public Scoreboard::Node {
public:
    uint32_t m_newScore;
    // CONSTRUCTORS
    explicit ScoreboardTestElem(uint32_t score)
        : m_newScore{score} {
        m_key.m_score = m_newScore;
        static uint32_t s_serial = 0;
        m_key.m_id = ++s_serial;
    }
    ScoreboardTestElem() = default;

    uint64_t id() const { return m_key.m_id; }
    void rescore() { m_key.m_score = m_newScore; }
    uint32_t score() const { return m_key.m_score; }
    static ScoreboardTestElem* heapNodeToElem(Scoreboard::Node* nodep) {
        return static_cast<ScoreboardTestElem*>(nodep);
    }
};

void V3ScoreboardBase::selfTest() {
    Scoreboard sb;

    UASSERT(!sb.needsRescore(), "SelfTest: Empty sb should not need rescore.");

    ScoreboardTestElem e1(10);
    ScoreboardTestElem e2(20);
    ScoreboardTestElem e3(30);

    sb.add(&e1);
    sb.add(&e2);
    sb.add(&e3);

    UASSERT(sb.needsRescore(), "SelfTest: Newly filled sb should need a rescore.");
    UASSERT(sb.needsRescore(&e1), "SelfTest: Individual newly-added element should need rescore");
    UASSERT(nullptr == sb.best(),
            "SelfTest: Newly filled sb should have nothing eligible for Bestp()");

    sb.rescore();

    UASSERT(!sb.needsRescore(), "SelfTest: Newly rescored sb should not need rescore");
    UASSERT(!sb.needsRescore(&e1),
            "SelfTest: Newly rescored sb should not need an element rescored");
    UASSERT(&e1 == sb.best(), "SelfTest: Should return element with lowest (best) score");

    // Change one element's score
    sb.hintScoreChanged(&e2);
    e2.m_newScore = 21;
    UASSERT(sb.needsRescore(&e2), "SelfTest: Should need rescore on elem after hintScoreChanged");

    // Remove an element
    UASSERT(sb.contains(&e1), "SelfTest: e1 should be there");
    sb.remove(&e1);
    UASSERT(!sb.contains(&e1), "SelfTest: e1 should be gone");
    UASSERT(sb.contains(&e2), "SelfTest: e2 should be there, despite needing rescore");

    // Now e3 should be our best-scoring element, even though
    // e2 has a better score, since e2 is pending rescore.
    UASSERT(&e3 == sb.best(), "SelfTest: Expect e3 as best element with known score.");
    sb.rescore();
    UASSERT(&e2 == sb.best(), "SelfTest: Expect e2 as best element again after Rescore");
}
