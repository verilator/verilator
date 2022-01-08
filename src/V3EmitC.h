// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ code for module tree
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

#ifndef VERILATOR_V3EMITC_H_
#define VERILATOR_V3EMITC_H_

#include "config_build.h"
#include "verilatedos.h"

//============================================================================

class V3EmitC final {
public:
    static void emitcConstPool();
    static void emitcHeaders();
    static void emitcImp();
    static void emitcInlines();
    static void emitcModel();
    static void emitcSyms(bool dpiHdrOnly = false);
    static void emitcFiles();
};

#endif  // Guard
