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
#include "V3FileLine.h"
#include "V3Parse.h"
#include "V3ParseSym.h"

namespace V3Builtin {
void parseStdPackage(V3Parse& parser) {
    string filename = v3Global.opt.hierTopDataDir() + "/builtin.v";
    std::ofstream* ofp = nullptr;
    ofp = V3File::new_ofstream(filename);
    if (!ofp->fail()) {
        *ofp << R"(
        package std;
            class process;
                integer x;
                function new();
                    x = 42;
                endfunction;
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
    }
    if (ofp) {
        ofp->close();
        delete ofp;
    }
    parser.parseFile(new FileLine(FileLine::commandLineFilename()), filename, false,
                     "Cannot find file with built-in definitions: ");
}

void defineExterns(AstNetlist* rootp, V3ParseSym& parseSyms) {
    auto* pkgp = rootp->modulesp();
    while (pkgp->name() != "std") { pkgp = VN_CAST(pkgp->nextp(), NodeModule); }
    parseSyms.pushNew(pkgp);
    auto* classp = parseSyms.symCurrentp()->findIdFallback("process")->nodep();
    auto* memberp = VN_CAST(classp, Class)->membersp();
    while (memberp) {
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
        memberp = memberp->nextp();
    }
    parseSyms.popScope(pkgp);
}

}  // namespace V3Builtin
