// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Insert DPI hooks at configured signal targets
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
// V3InsertDPIHook's Transformations:
// The hook-insertion configuration map is populated with the relevant nodes, as defined by the
// target string specified in the hook-insertion configuration within the .vlt file.
// Additionally, the AST (Abstract Syntax Tree) is modified to insert the necessary extra nodes
// required for calling the DPI hooks.
// Furthermore, the links between Module, Cell, and Var nodes are adjusted to ensure correct
// connectivity for the DPI hook purposes.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3InsertDPIHook.h"

VL_DEFINE_DEBUG_FUNCTIONS;

void V3InsertDPIHook::hookInsert(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    V3Global::dumpCheckGlobalTree("insertDpiHook", 0, dumpTreeEitherLevel() >= 3);
}
