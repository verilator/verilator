// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Link XREF signals/functions together
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

#ifndef VERILATOR_V3LINKDOT_H_
#define VERILATOR_V3LINKDOT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3ThreadSafety.h"

//============================================================================

enum VLinkDotStep : uint8_t { LDS_PRIMARY, LDS_PARAMED, LDS_ARRAYED, LDS_SCOPED };

class V3LinkDot final {
    static void linkDotGuts(AstNetlist* rootp, VLinkDotStep step) VL_MT_DISABLED;

public:
    static void linkDotPrimary(AstNetlist* nodep) VL_MT_DISABLED;
    static void linkDotParamed(AstNetlist* nodep) VL_MT_DISABLED;
    static void linkDotArrayed(AstNetlist* nodep) VL_MT_DISABLED;
    static void linkDotScope(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
