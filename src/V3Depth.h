// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prevent very deep expressions
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

#ifndef VERILATOR_V3DEPTH_H_
#define VERILATOR_V3DEPTH_H_

#include "config_build.h"
#include "verilatedos.h"

#include <vector>

class AstNetlist;
class AstNodeAssign;
class AstNodeModule;

//============================================================================

class V3Depth final {
public:
    static void depthAll(AstNetlist* nodep) VL_MT_DISABLED;
    // Break expression spines so later visitors do not use one C frame per node.
    // Width calls this on an assignment after the preliminary width walk, when
    // dtypes exist and the final walk would otherwise recurse down the spine.
    // markWidthed is true once V3WidthCommit has already run.
    static std::vector<AstNodeAssign*> breakDeepAssign(AstNodeAssign* assignp,
                                                       AstNodeModule* modp,
                                                       bool markWidthed) VL_MT_DISABLED;
    static void breakDeepExprs(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
