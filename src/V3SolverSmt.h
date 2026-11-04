// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: SMT-LIB constraint solver back-end
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3SOLVERSMT_H_
#define VERILATOR_V3SOLVERSMT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3SolverBackend.h"

class V3SolverSmt final {
public:
    static std::unique_ptr<V3SolverBackend> newBackend(VMemberMap& memberMap,
                                                       V3UniqueNames& uniqueNames,
                                                       const RandModeVars& modeVars,
                                                       VNDeleter& deleter) VL_MT_DISABLED;
    static V3SolverRuntime runtime() VL_MT_DISABLED;
    static std::vector<std::string> runtimeCFlags() VL_MT_DISABLED;
};

#endif  // Guard
