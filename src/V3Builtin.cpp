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
#include "V3Builtin.h"
#include "V3Parse.h"
#include "V3ParseSym.h"

void V3Builtin::parseStdPackage(V3Parse& parser) {
    string path = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__builtin.v";
    auto ofp = std::unique_ptr<std::ofstream>(V3File::new_ofstream(path));
    if (!ofp || ofp->fail()) {
        FileLine fl(FileLine::commandLineFilename());
        fl.v3error("Could not open file '" + path + "' for writing");
    } else {
        *ofp << R"(
        package std;
            class process;
                typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;
                extern static function process self();
                extern function state status();
                extern function void kill();
                extern task await();
                extern function void suspend();
                extern function void resume();
            endclass
        endpackage
        )" << std::endl;
        ofp->close();
    }
    parser.parseFile(new FileLine(FileLine::commandLineFilename()), path, false,
                     "Cannot find file containing built-in definitions: ");
}

void V3Builtin::defineExterns(AstNetlist* rootp, V3ParseSym& parseSyms) {
    auto* pkgp = rootp->modulesp();
    while (pkgp->name() != "std") { pkgp = VN_CAST(pkgp->nextp(), NodeModule); }
    UASSERT_OBJ(pkgp, rootp, "std:: package not found");
    parseSyms.pushNew(pkgp);
    auto* classp = VN_CAST(parseSyms.symCurrentp()->findIdFallback("process")->nodep(), Class);
    UASSERT_OBJ(pkgp, rootp, "std::process class not found");
    classp->isStdProcess(true);
    for (auto* memberp = classp->membersp(); memberp; memberp = memberp->nextp()) {
        AstNodeFTask* ftaskp = nullptr;
        if (VN_IS(memberp, Task)) {
            ftaskp = new AstTask(rootp->fileline(), memberp->name(), nullptr);
        } else if (memberp->name() == "status") {
            ftaskp = new AstFunc(
                rootp->fileline(), memberp->name(), nullptr,
                new AstRefDType(
                    memberp->fileline(), "state",
                    new AstClassOrPackageRef(memberp->fileline(), classp->name(), classp, nullptr),
                    nullptr));
        } else if (memberp->name() == "self") {
            ftaskp = new AstFunc(
                rootp->fileline(), memberp->name(), nullptr,
                new AstRefDType(memberp->fileline(), classp->name(), nullptr, nullptr));
            ftaskp->lifetime(VLifetime::STATIC);
            ftaskp->addStmtsp(
                new AstReturn(classp->fileline(), new AstNew(memberp->fileline(), nullptr)));
        }
        if (ftaskp) {
            ftaskp->packagep(
                new AstClassOrPackageRef(memberp->fileline(), classp->name(), classp, nullptr));
            pkgp->addActivep(ftaskp);
        }
    }
    parseSyms.popScope(pkgp);
}
