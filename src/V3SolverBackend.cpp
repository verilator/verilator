// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Constraint solver back-end selection
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
// Back-end selection, and the definitions shared by the randomize front end
// and the back-ends. The SMT-LIB back-end (V3SolverSmt) is the only back-end,
// so it is always selected. See V3SolverBackend.h for the interface.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SolverBackend.h"

#include "V3SolverSmt.h"

std::unique_ptr<V3SolverBackend> V3SolverBackend::create(VMemberMap& memberMap,
                                                         V3UniqueNames& uniqueNames,
                                                         const RandModeVars& modeVars,
                                                         VNDeleter& deleter) {
    return V3SolverSmt::newBackend(memberMap, uniqueNames, modeVars, deleter);
}

V3SolverRuntime V3SolverBackend::runtime() { return V3SolverSmt::runtime(); }

std::vector<std::string> V3SolverBackend::runtimeCFlags() { return V3SolverSmt::runtimeCFlags(); }

AstVar* RandModeVars::randModeVarp(AstNodeModule* classp) {
    while (classp) {
        if (classp->user2p()) return VN_AS(classp->user2p(), Var);
        AstClass* const cp = VN_CAST(classp, Class);
        if (!cp || !cp->extendsp()) return nullptr;
        classp = cp->extendsp()->classp();
    }
    return nullptr;
}

AstNode* RandModeVars::wrapIfMode(const RandomizeMode mode, AstVar* modeVarp, AstNode* stmtp) {
    FileLine* const fl = stmtp->fileline();
    if (mode.usesMode) {
        // user2p can be either AstClass or AstClassPackage (for static constraints)
        AstNodeModule* const modp = VN_AS(modeVarp->user2p(), NodeModule);
        AstCMethodHard* const atp
            = new AstCMethodHard{fl, new AstVarRef{fl, modp, modeVarp, VAccess::READ},
                                 VCMethod::ARRAY_AT, new AstConst{fl, mode.index}};
        atp->dtypeSetUInt32();
        return new AstIf{fl, atp, stmtp};
    }
    return stmtp;
}

AstVar* RandModeVars::staticConstraintModeVarp(AstClass* classp) const {
    const auto it = staticConstraintModeVars.find(classp);
    if (it != staticConstraintModeVars.end()) return it->second;
    if (AstClassExtends* const extendsp = classp->extendsp()) {
        return staticConstraintModeVarp(extendsp->classp());
    }
    return nullptr;
}

AstVar* RandModeVars::staticRandModeVarp(AstClass* classp) const {
    const auto it = staticRandModeVars.find(classp);
    if (it != staticRandModeVars.end()) return it->second;
    if (AstClassExtends* const extendsp = classp->extendsp()) {
        return staticRandModeVarp(extendsp->classp());
    }
    return nullptr;
}

AstVar* RandModeVars::constraintModeVarp(AstClass* classp) {
    if (classp->user4p()) return VN_AS(classp->user4p(), Var);
    if (AstClassExtends* const extendsp = classp->extendsp()) {
        return constraintModeVarp(extendsp->classp());
    }
    return nullptr;
}
