// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Possible targets of calls
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

#ifndef VERILATOR_V3CALLTARGETS_H_
#define VERILATOR_V3CALLTARGETS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <memory>
#include <unordered_map>
#include <vector>

//============================================================================

// The functions an AstNodeCCall may call, including through virtual functions
class V3CallTargets final {
    // MEMBERS
    // Function -> The functions directly overriding it, in any derived class
    std::unordered_map<const AstCFunc*, std::vector<AstCFunc*>> m_overriderps;
    // Called function -> The functions a dynamically dispatched call of it may resolve to. An
    // empty entry is not computed yet, as it always holds the called function.
    mutable std::unordered_map<const AstCFunc*, std::vector<AstCFunc*>> m_dynamicCalleeps;
    // Called function -> Just itself, for statically dispatched (super) calls
    mutable std::unordered_map<const AstCFunc*, std::vector<AstCFunc*>> m_staticCalleeps;

    // CONSTRUCTORS
    V3CallTargets();  // Only made by build()

    // METHODS
    const std::vector<AstCFunc*>& getDynCallees(AstCFunc* funcp) const;

public:
    // Builds the call targets for the whole netlist, this is the only way to acquire an instance
    static std::unique_ptr<V3CallTargets> build();

    // Returns the AstCFuncs that 'callp' may call, in a deterministic order: 'callp->funcp()'
    // itself first, then, unless it is a super call, which is statically dispatched, the
    // functions overriding it, depth-first.
    const std::vector<AstCFunc*>& getTargets(const AstNodeCCall* callp) const;
};

#endif  // Guard
