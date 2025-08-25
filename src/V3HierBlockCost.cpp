// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Fetch or eval hier_block costs for scheduling
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3HierBlockCost.h"

#include "V3Ast.h"
#include "V3Control.h"
#include "V3Global.h"
#include "V3InstrCount.h"

VL_DEFINE_DEBUG_FUNCTIONS;

void V3HierBlockCost::evaluate() {
    if (uint64_t cost = V3Control::getProfileData(v3Global.opt.prefix())) {
        UINFO(9, "Fetching cost from profile info: " << cost);
        v3Global.hierDpiCost(cost);
    } else {
        // The `eval` function is called inside both update functions. As those functions
        // are created by text bashing, we need to find cost of `_eval` which is the first
        // function with a real cost in the AST.
        const bool evalFuncExists
            = v3Global.rootp()->topModulep()->exists([&cost](AstCFunc* cfuncp) {
                  if (cfuncp->name() == "_eval") {
                      cost = V3InstrCount::count(cfuncp, false);
                      return true;
                  }
                  return false;
              });
        UASSERT(evalFuncExists, "Top level eval function need to exist at this stage");
        UINFO(9, "Evaluating cost: " << cost);
        v3Global.hierDpiCost(cost);
    }
}
