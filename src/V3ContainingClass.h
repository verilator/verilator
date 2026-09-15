// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cached containing-class lookup
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

#ifndef VERILATOR_V3CONTAININGCLASS_H_
#define VERILATOR_V3CONTAININGCLASS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <unordered_map>

//######################################################################

class V3ContainingClassFinder final {
    // The cache stores the class containing each node, excluding the node itself when it is a
    // class. This lets recursion through preceding siblings reuse the same ownership result.
    std::unordered_map<const AstNode*, AstClass*> m_cache;

    AstClass* findCached(AstNode* nodep) {
        if (!nodep) return nullptr;
        const auto it = m_cache.find(nodep);
        if (it != m_cache.end()) return it->second;

        AstClass* classp = nullptr;
        if (nodep->backp() && nodep->backp()->nextp() == nodep) {
            classp = findCached(nodep->backp());
        } else if (AstClass* const parentp = VN_CAST(nodep->backp(), Class)) {
            classp = parentp;
        } else if (AstClassPackage* const packagep = VN_CAST(nodep->backp(), ClassPackage)) {
            classp = packagep->classp();
        } else {
            classp = findCached(nodep->backp());
        }
        m_cache.emplace(nodep, classp);
        return classp;
    }

public:
    AstClass* find(AstNode* nodep) {
        if (AstClass* const classp = VN_CAST(nodep, Class)) return classp;
        if (AstClassPackage* const packagep = VN_CAST(nodep, ClassPackage)) {
            return packagep->classp();
        }
        return findCached(nodep);
    }
};

#endif  // Guard
