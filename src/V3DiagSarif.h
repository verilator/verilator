// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Diag Sarif output file
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

#ifndef VERILATOR_V3DIAGSARIF_H_
#define VERILATOR_V3DIAGSARIF_H_

#include "config_build.h"
#include "verilatedos.h"

#include <V3Error.h>

//============================================================================

class V3DiagSarif final {
public:
    static void pushMessage(const VErrorMessage& msg) VL_MT_DISABLED;
    static void output(bool success) VL_MT_DISABLED;
};

#endif  // Guard
