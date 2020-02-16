// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break variables into separate words to avoid UNOPTFLAT
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3SPLITVAR_H_
#define _V3SPLITVAR_H_ 1

//============================================================================

class AstNetlist;
class AstVar;

class V3SplitVar {
public:
    // Split variables marked with split_var metacomment.
    static void splitVariable(AstNetlist* nodep);

    // Return true if the variable can be split.
    // This check is not perfect.
    static bool canSplitVar(const AstVar* varp);
};

#endif  // Guard
