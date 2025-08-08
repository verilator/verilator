// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Evaluate hier_block costs for scheduling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3HIERDPICOST_H_
#define VERILATOR_V3HIERDPICOST_H_

#include "config_build.h"
#include "verilatedos.h"

//============================================================================

class V3HierBlockCost final {
public:
    static void evaluate();
};

#endif  // guard
