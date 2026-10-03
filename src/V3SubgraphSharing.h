// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Receiver-independent subgraph procedure sharing
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

#ifndef VERILATOR_V3SUBGRAPHSHARING_H_
#define VERILATOR_V3SUBGRAPHSHARING_H_

#include "config_build.h"
#include "verilatedos.h"

#include <memory>

class AstCell;
class AstNetlist;
class AstNodeExpr;
class AstNodeModule;
class AstVar;

// Analyze sharing before Scope expands procedures. The shared module body
// reads per-instance input captures instead of specializing on connections.
class V3SubgraphSharing final {
    struct Impl;
    const std::unique_ptr<Impl> m_impl;  // Sharing analysis retained during pin lowering

public:
    static bool shareableModuleShape(const AstNodeModule* modp);

    explicit V3SubgraphSharing(AstNetlist* netlistp);
    ~V3SubgraphSharing();
    VL_UNCOPYABLE(V3SubgraphSharing);

    AstNodeExpr* clockExpression(AstCell* cellp);
    void captureInput(AstCell* cellp, AstVar* portp, AstNodeExpr* exprp, AstNodeExpr* clockp);
};

#endif  // Guard
