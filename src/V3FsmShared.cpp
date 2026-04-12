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

#include "V3PchAstNoMT.h"

#include "V3FsmShared.h"

#include "V3Ast.h"

V3FsmRegistry& V3FsmRegistry::instance() {
    static V3FsmRegistry s_registry;
    return s_registry;
}

void V3FsmRegistry::clear() {
    m_byVar.clear();
}

bool V3FsmRegistry::has(const AstVarScope* vscp) const { return m_byVar.find(vscp) != m_byVar.end(); }

V3FsmDesc* V3FsmRegistry::find(const AstVarScope* vscp) {
    const auto it = m_byVar.find(vscp);
    return it == m_byVar.end() ? nullptr : &it->second;
}

V3FsmDesc& V3FsmRegistry::upsert(const AstVarScope* vscp) { return m_byVar[vscp]; }
