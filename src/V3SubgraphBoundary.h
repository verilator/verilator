// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Subgraph boundary metadata and phase checks
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

#ifndef VERILATOR_V3SUBGRAPHBOUNDARY_H_
#define VERILATOR_V3SUBGRAPHBOUNDARY_H_

#include "config_build.h"
#include "verilatedos.h"

#include <memory>

class AstNetlist;
class AstScope;
class FileLine;
class AstNodeModule;
class AstNodeExpr;
class AstVarRef;

class V3SubgraphBoundary final {
    struct Impl;
    const std::unique_ptr<Impl> m_impl;  // Metadata retained across compiler stages

public:
    static const AstVarRef* writtenCombinationalVarRef(const AstNodeExpr* lhsp);

    explicit V3SubgraphBoundary(AstNetlist* netlistp);
    ~V3SubgraphBoundary();
    VL_UNCOPYABLE(V3SubgraphBoundary);

    void prepare(AstNetlist* netlistp);
    void scoped(AstNetlist* netlistp);
    FileLine* externalAccessFileline(const AstScope* scopep) const;
    void delayed(AstNetlist* netlistp);
    void scheduled(AstNetlist* netlistp);
};

#endif  // Guard
