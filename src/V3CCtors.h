// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit CFunc's for class construction and configuration
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

#ifndef VERILATOR_V3CCTORS_H_
#define VERILATOR_V3CCTORS_H_

#include "config_build.h"
#include "verilatedos.h"

//============================================================================

class V3CCtors final {
public:
    static void cctorsAll();

private:
    static void evalAsserts();
};

#endif  // Guard
