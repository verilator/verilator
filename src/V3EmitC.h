// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ code for module tree
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

#ifndef VERILATOR_V3EMITC_H_
#define VERILATOR_V3EMITC_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3ThreadSafety.h"

//============================================================================

class V3EmitC final {
public:
    static void emitcConstPool() VL_MT_DISABLED;
    static void emitcFiles() VL_MT_DISABLED;
    static void emitcHeaders() VL_MT_DISABLED;
    static void emitcImp();
    static void emitcInlines() VL_MT_DISABLED;
    static void emitcModel() VL_MT_DISABLED;
    static void emitcPch() VL_MT_DISABLED;
    static void emitcSyms(bool dpiHdrOnly = false) VL_MT_DISABLED;
};

#endif  // Guard
