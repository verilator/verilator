// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper program
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2004-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PRESHELL_H_
#define VERILATOR_V3PRESHELL_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"

class V3ParseImp;
class VInFilter;
class VSpellCheck;

//============================================================================

// $coverage_control arguments and results (IEEE 1800-2023 20.14), predefined as `SV_COV_*.
// VL_COVERAGE_CONTROL in include/verilated_cov.h uses some of these values.
struct VSvCov final {
    enum en : int8_t {
        SV_COV_START = 0,
        SV_COV_STOP = 1,
        SV_COV_RESET = 2,
        SV_COV_CHECK = 3,
        SV_COV_MODULE = 10,
        SV_COV_HIER = 11,
        SV_COV_ASSERTION = 20,
        SV_COV_FSM_STATE = 21,
        SV_COV_STATEMENT = 22,
        SV_COV_TOGGLE = 23,
        // Extensions also used by other simulators
        SV_COV_LINE = -102,
        SV_COV_BRANCH = -104,
        SV_COV_CONDITION = -105,
        SV_COV_EXPRESSION = -106,
        SV_COV_EXPR = -106,
        SV_COV_FSM_TRANS = -107,
        SV_COV_ALL = -110,
        // Results
        SV_COV_OVERFLOW = -2,
        SV_COV_ERROR = -1,
        SV_COV_NOCOV = 0,
        SV_COV_OK = 1,
        SV_COV_PARTIAL = 2
    };
};

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
    static void selfTest() VL_MT_DISABLED;
};

#endif  // Guard
