// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ORDER_H_
#define VERILATOR_V3ORDER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3ThreadSafety.h"

#include <functional>
#include <unordered_map>
#include <vector>

class AstCFunc;
class AstNetlist;
class AstSenItem;
class AstSenTree;
class AstVarScope;

namespace V3Sched {
struct LogicByScope;
};  // namespace V3Sched

//============================================================================

namespace V3Order {

using ExternalDomainsProvider = std::function<void(const AstVarScope*, std::vector<AstSenTree*>&)>;

AstCFunc* order(
    AstNetlist* netlistp,  //
    const std::vector<V3Sched::LogicByScope*>& logic,  //
    const std::unordered_map<const AstSenItem*, const AstSenTree*>& trigToSen,
    const string& tag,  //
    bool parallel,  //
    bool slow,  //
    const ExternalDomainsProvider& externalDomains
    = [](const AstVarScope*, std::vector<AstSenTree*>&) {}) VL_MT_DISABLED;

};  // namespace V3Order

#endif  // Guard
