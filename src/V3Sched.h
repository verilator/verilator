// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling
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

#ifndef VERILATOR_V3SCHED_H_
#define VERILATOR_V3SCHED_H_

#include "config_build.h"
#include "verilatedos.h"

#include <utility>
#include <vector>

class AstScope;
class AstActive;
class AstExecGraph;
class AstNetlist;
class AstCFunc;

//============================================================================

namespace V3Sched {

struct LogicByScope final : public std::vector<std::pair<AstScope*, std::vector<AstActive*>>> {
    // Create copy, with the AstActives cloned
    LogicByScope clone() const;
};

void schedule(AstNetlist*);

void splitCheck(AstCFunc* funcp);

std::vector<AstActive*> orderST(AstNetlist*, const std::vector<const V3Sched::LogicByScope*>&,
                                bool);
AstExecGraph* orderMT(AstNetlist*, const std::vector<const V3Sched::LogicByScope*>&);
};  // namespace V3Sched

#endif  // Guard
