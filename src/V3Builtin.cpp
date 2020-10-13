// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: built-in packages and classes
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

#include "V3Builtin.h"
#include "V3FileLine.h"

namespace V3Builtin {

void defineProcessClass(AstNetlist* rootp, V3ParseSym& parseSyms) {
    auto* processClassp = new AstClass(rootp->fileline(), "process");
    // Member tasks
    auto* killTaskp = new AstTask(rootp->fileline(), "kill", nullptr);
    processClassp->addMembersp(killTaskp);
    auto* awaitTaskp = new AstTask(rootp->fileline(), "await", nullptr);
    processClassp->addMembersp(awaitTaskp);
    auto* suspendTaskp = new AstTask(rootp->fileline(), "suspend", nullptr);
    processClassp->addMembersp(suspendTaskp);
    auto* resumeTaskp = new AstTask(rootp->fileline(), "resume", nullptr);
    processClassp->addMembersp(resumeTaskp);

    // Unit package for the class
    auto* unitPackagep = rootp->dollarUnitPkgAddp();
    parseSyms.reinsert(unitPackagep, parseSyms.symRootp());
    unitPackagep->addStmtp(processClassp);

    // Create a 'process' package to emulate static functions
    auto* processPackagep = new AstPackage(rootp->fileline(), "process__Vpkg");
    auto* selfFuncp = new AstFunc(rootp->fileline(), "self", nullptr,
                                  new AstClassRefDType(rootp->fileline(), processClassp));
    rootp->addModulep(processPackagep);
    parseSyms.pushNew(processPackagep);
    processPackagep->addStmtp(selfFuncp);
    processPackagep->inLibrary(true);
    processPackagep->lifetime(VLifetime::NONE);
    parseSyms.pushNew(selfFuncp);
    parseSyms.popScope(selfFuncp);
    parseSyms.popScope(processPackagep);
}

}  // namespace V3Builtin
