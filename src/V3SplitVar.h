// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break variables into separate words to avoid UNOPTFLAT
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

#ifndef VERILATOR_V3SPLITVAR_H_
#define VERILATOR_V3SPLITVAR_H_

//============================================================================

class AstNetlist;
class AstVar;

class V3SplitVar final {
public:
    // Split variables marked with split_var metacomment.
    static void splitVariable(AstNetlist* nodep);

    // Return true if the variable can be split.
    // This check is not perfect.
    static bool canSplitVar(const AstVar* varp);
};

#endif  // Guard
