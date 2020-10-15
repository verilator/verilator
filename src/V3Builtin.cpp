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

#include "V3Ast.h"
#include "V3FileLine.h"
#include "V3ParseSym.h"

void V3Builtin::makeProcessClass(AstNetlist* rootp, V3ParseSym& parseSyms) {
    m_processClassp = new AstClass(rootp->fileline(), "process__builtin_cls");

    // Member tasks
    auto* killTaskp = new AstTask(rootp->fileline(), "kill", nullptr);
    auto* awaitTaskp = new AstTask(rootp->fileline(), "await", nullptr);
    auto* suspendTaskp = new AstTask(rootp->fileline(), "suspend", nullptr);
    auto* resumeTaskp = new AstTask(rootp->fileline(), "resume", nullptr);
    auto* srandomTaskp = new AstTask(rootp->fileline(), "srandom", nullptr);
    auto* getRandstateTaskp = new AstTask(rootp->fileline(), "get_randstate", nullptr);
    auto* setRandstateTaskp = new AstTask(rootp->fileline(), "set_randstate", nullptr);
    m_processClassp->addMembersp(killTaskp);
    m_processClassp->addMembersp(awaitTaskp);
    m_processClassp->addMembersp(suspendTaskp);
    m_processClassp->addMembersp(resumeTaskp);
    m_processClassp->addMembersp(srandomTaskp);
    m_processClassp->addMembersp(getRandstateTaskp);
    m_processClassp->addMembersp(setRandstateTaskp);

    // Unit package for the class
    auto* unitPackagep = rootp->dollarUnitPkgAddp();
    parseSyms.reinsert(unitPackagep, parseSyms.symRootp());
    unitPackagep->addStmtp(m_processClassp);

    // Create a 'process' package to emulate static functions
    m_processPackagep = new AstPackage(rootp->fileline(), "process__builtin_pkg");
    m_processPackagep->inLibrary(true);
    rootp->addModulep(m_processPackagep);
    parseSyms.pushNew(m_processPackagep);

    // Function 'process::self'
    auto* selfFuncp = new AstFunc(rootp->fileline(), "self", nullptr,
                                  new AstClassRefDType(rootp->fileline(), m_processClassp));
    m_processPackagep->addStmtp(selfFuncp);
    parseSyms.pushNew(selfFuncp);
    parseSyms.popScope(selfFuncp);

    // Enum 'process::state'
    auto* finishedEnumItemp = new AstEnumItem(rootp->fileline(), "FINISHED", nullptr, nullptr);
    auto* runningEnumItemp = new AstEnumItem(rootp->fileline(), "RUNNING", nullptr, nullptr);
    auto* waitingEnumItemp = new AstEnumItem(rootp->fileline(), "WAITING", nullptr, nullptr);
    auto* suspendedEnumItemp = new AstEnumItem(rootp->fileline(), "SUSPENDED", nullptr, nullptr);
    auto* killedEnumItemp = new AstEnumItem(rootp->fileline(), "KILLED", nullptr, nullptr);
    finishedEnumItemp->addNext(runningEnumItemp);
    runningEnumItemp->addNext(waitingEnumItemp);
    waitingEnumItemp->addNext(suspendedEnumItemp);
    suspendedEnumItemp->addNext(killedEnumItemp);
    auto* stateEnump = new AstEnumDType(
        rootp->fileline(), VFlagChildDType(),
        new AstBasicDType(rootp->fileline(), AstBasicDTypeKwd::INT), finishedEnumItemp);
    auto* stateTypedefp
        = new AstTypedef(rootp->fileline(), "state", nullptr, VFlagChildDType(), stateEnump);
    m_processPackagep->addStmtp(stateTypedefp);
    parseSyms.pushNew(stateTypedefp);
    parseSyms.popScope(stateTypedefp);

    parseSyms.popScope(m_processPackagep);

    // Member function 'status'
    auto* statusFuncp = new AstFunc(
        rootp->fileline(), "status", nullptr,
        new AstRefDType(rootp->fileline(), "state",
                        new AstClassOrPackageRef(rootp->fileline(), "process__builtin_pkg",
                                                 m_processPackagep, nullptr),
                        nullptr));
    m_processClassp->addMembersp(statusFuncp);
}
