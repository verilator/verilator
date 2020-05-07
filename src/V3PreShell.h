// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper program
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3PRESHELL_H_
#define _V3PRESHELL_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"

class V3ParseImp;
class VInFilter;
class VSpellCheck;

//============================================================================

class V3PreShell {
    // Static class for calling preprocessor
public:
    static void boot(char** env);
    static bool preproc(FileLine* fl, const string& modname, VInFilter* filterp,
                        V3ParseImp* parsep, const string& errmsg);
    static void preprocInclude(FileLine* fl, const string& modname);
    static void defineCmdLine(const string& name, const string& value);
    static void undef(const string& name);
    static void dumpDefines(std::ostream& os);
    static void candidateDefines(VSpellCheck* spellerp);
};

#endif  // Guard
