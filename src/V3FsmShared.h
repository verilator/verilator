// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: FSM coverage shared metadata
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3FSMSHARED_H_
#define VERILATOR_V3FSMSHARED_H_

#include "config_build.h"
#include "verilatedos.h"

#include <unordered_map>
#include <utility>
#include <vector>

class AstNodeExpr;
class AstScope;
class AstVar;
class AstVarScope;
class FileLine;
class V3FsmSenDesc final {
public:
    uint8_t edgeType = 0;
    AstVarScope* vscp = nullptr;
    bool negated = false;
};

class V3FsmResetCondDesc final {
public:
    AstVarScope* vscp = nullptr;
    bool negated = false;
};

struct V3FsmArcDesc final {
    string fromLabel;
    int fromValue = 0;
    string toLabel;
    int toValue = 0;
    bool isReset = false;
    bool isCond = false;
    bool isDefault = false;
    FileLine* flp = nullptr;
};

struct V3FsmDesc final {
    AstVar* stateVarp = nullptr;
    AstVarScope* stateVscp = nullptr;
    AstScope* scopep = nullptr;
    string stateVarName;
    std::vector<std::pair<string, int>> states;
    std::vector<V3FsmArcDesc> arcs;
    std::vector<V3FsmSenDesc> senses;
    V3FsmResetCondDesc resetCond;
    bool hasResetCond = false;
    bool resetInclude = false;
    bool inclCond = false;
    FileLine* flp = nullptr;
};

class V3FsmRegistry final {
    std::unordered_map<const AstVarScope*, V3FsmDesc> m_byVar;

public:
    static V3FsmRegistry& instance();
    void clear();
    bool has(const AstVarScope* vscp) const;
    V3FsmDesc* find(const AstVarScope* vscp);
    const std::unordered_map<const AstVarScope*, V3FsmDesc>& all() const { return m_byVar; }
    V3FsmDesc& upsert(const AstVarScope* vscp);
};

#endif
