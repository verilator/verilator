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

class V3SolverSmt final : public V3SolverBackend {
public:
    std::string runtimeHeader() const override VL_MT_DISABLED { return "verilated_random.h"; }
    std::vector<std::string> runtimeCppFiles() const override VL_MT_DISABLED {
        return {"verilated_random.cpp"};
    }
    std::vector<std::string> runtimeCFlags() const override VL_MT_DISABLED;
    std::unique_ptr<V3SolverLowering>
    newLowering(VMemberMap& memberMap, V3UniqueNames& uniqueNames, const RandModeVars& modeVars,
                VNDeleter& deleter) const override VL_MT_DISABLED;
};

#endif  // Guard
