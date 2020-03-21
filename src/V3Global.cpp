// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common implemenetations
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Ast.h"
#include "V3File.h"
#include "V3LinkCells.h"
#include "V3Parse.h"
#include "V3ParseSym.h"
#include "V3Stats.h"

//######################################################################
// V3 Class -- top level

AstNetlist* V3Global::makeNetlist() {
    AstNetlist* newp = new AstNetlist();
    newp->addTypeTablep(new AstTypeTable(newp->fileline()));
    return newp;
}

void V3Global::checkTree() { rootp()->checkTree(); }

void V3Global::clear() {
    if (m_rootp) VL_DO_CLEAR(m_rootp->deleteTree(), m_rootp = NULL);
}

void V3Global::readFiles() {
    // NODE STATE
    //   AstNode::user4p()      // VSymEnt*    Package and typedef symbol names
    AstUser4InUse inuser4;

    VInFilter filter(v3Global.opt.pipeFilter());
    V3ParseSym parseSyms(v3Global.rootp());  // Symbol table must be common across all parsing

    V3Parse parser(v3Global.rootp(), &filter, &parseSyms);
    // Read top module
    const V3StringList& vFiles = v3Global.opt.vFiles();
    for (V3StringList::const_iterator it = vFiles.begin(); it != vFiles.end(); ++it) {
        string filename = *it;
        parser.parseFile(new FileLine(FileLine::commandLineFilename()), filename, false,
                         "Cannot find file containing module: ");
    }

    // Read libraries
    // To be compatible with other simulators,
    // this needs to be done after the top file is read
    const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
    for (V3StringSet::const_iterator it = libraryFiles.begin(); it != libraryFiles.end(); ++it) {
        string filename = *it;
        parser.parseFile(new FileLine(FileLine::commandLineFilename()), filename, true,
                         "Cannot find file containing library module: ");
    }
    // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("parse.tree"));
    V3Error::abortIfErrors();

    if (!v3Global.opt.preprocOnly()) {
        // Resolve all modules cells refer to
        V3LinkCells::link(v3Global.rootp(), &filter, &parseSyms);
    }
}

void V3Global::dumpCheckGlobalTree(const string& stagename, int newNumber, bool doDump) {
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename(stagename + ".tree", newNumber),
                                   false, doDump);
    if (v3Global.opt.stats()) V3Stats::statsStage(stagename);
}
