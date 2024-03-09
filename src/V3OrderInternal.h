// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERINTERNAL_H_
#define VERILATOR_V3ORDERINTERNAL_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Order.h"
#include "V3OrderGraph.h"
#include "V3ThreadSafety.h"

#include <string>
#include <unordered_map>
#include <vector>

class AstNetlist;
class AstSenItem;
class AstSenTree;

namespace V3Sched {
struct LogicByScope;
};  // namespace V3Sched

//============================================================================

namespace V3Order {

std::unique_ptr<OrderGraph> buildOrderGraph(AstNetlist* netlistp,  //
                                            const std::vector<V3Sched::LogicByScope*>& coll,  //
                                            const TrigToSenMap& trigToSen);

void orderOrderGraph(OrderGraph& graph, const std::string& tag);

void processDomains(AstNetlist* netlistp,  //
                    OrderGraph& graph,  //
                    const std::string& tag,  //
                    const TrigToSenMap& trigToSen,  //
                    const ExternalDomainsProvider& externalDomains);

std::vector<AstActive*> createSerial(const OrderGraph& graph,  //
                                     const std::string& tag,  //
                                     const TrigToSenMap& trigToSenMap,  //
                                     bool slow);

AstExecGraph* createParallel(const OrderGraph& graph,  //
                             const std::string& tag,  //
                             const TrigToSenMap& trigToSenMap,  //
                             bool slow);

};  // namespace V3Order

#endif  // Guard
