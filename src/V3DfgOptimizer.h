// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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

#ifndef VERILATOR_V3DFGOPTIMIZER_H_
#define VERILATOR_V3DFGOPTIMIZER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

//============================================================================

namespace V3DfgOptimizer {
// Extract further logic blocks from the design for additional optimization opportunities
void extract(AstNetlist*);

// Optimize the design
void optimize(AstNetlist*, const string& label);
}  // namespace V3DfgOptimizer

#endif  // Guard
