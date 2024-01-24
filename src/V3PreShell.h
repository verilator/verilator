// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper program
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PRESHELL_H_
#define VERILATOR_V3PRESHELL_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3ThreadSafety.h"

class V3ParseImp;
class VInFilter;
class VSpellCheck;

//============================================================================

class V3PreShell final {
    // Static class for calling preprocessor
public:
    static void boot() VL_MT_DISABLED;
    static void shutdown() VL_MT_DISABLED;
    static bool preproc(FileLine* fl, const string& modname, VInFilter* filterp,
                        V3ParseImp* parsep, const string& errmsg) VL_MT_DISABLED;
    static void preprocInclude(FileLine* fl, const string& modname) VL_MT_DISABLED;
    static void defineCmdLine(const string& name, const string& value) VL_MT_DISABLED;
    static void undef(const string& name) VL_MT_DISABLED;
    static void dumpDefines(std::ostream& os) VL_MT_DISABLED;
    static void candidateDefines(VSpellCheck* spellerp) VL_MT_DISABLED;
};

#endif  // Guard
