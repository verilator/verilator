// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit CMake file list
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3EMITCMAKE_H_
#define _V3EMITCMAKE_H_ 1

#include "config_build.h"
#include "verilatedos.h"

//============================================================================

class V3EmitCMake {
public:
    static void emit();
};

#endif  // Guard
