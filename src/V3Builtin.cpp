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
    auto* processPackagep = new AstPackage(rootp->fileline(), "process");
    auto* selfFuncp = new AstFunc(rootp->fileline(), "self", nullptr,
                                  new AstBasicDType(rootp->fileline(), AstBasicDTypeKwd::LOGIC));
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
