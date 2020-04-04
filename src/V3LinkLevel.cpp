// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// LINKTOP TRANSFORMATIONS:
//      Utility functions
//          Sort cells by depth
//          Create new MODULE TOP with connections to below signals
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3LinkLevel.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <map>
#include <vector>

//######################################################################
// Levelizing class functions

struct CmpLevel {
    inline bool operator() (const AstNodeModule* lhsp, const AstNodeModule* rhsp) const {
        return lhsp->level() < rhsp->level();
    }
};

void V3LinkLevel::modSortByLevel() {
    // Sort modules by levels, root down to lowest children
    // Calculate levels again in case we added modules
    UINFO(2,"modSortByLevel()\n");

    // level() was computed for us in V3LinkCells

    typedef std::vector<AstNodeModule*> ModVec;

    ModVec mods;  // Modules
    ModVec tops;  // Top level modules
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_CAST(nodep->nextp(), NodeModule)) {
        if (nodep->level() <= 2) tops.push_back(nodep);
        mods.push_back(nodep);
    }
    if (tops.size() >= 2) {
        AstNode* secp = tops[1];  // Complain about second one, as first often intended
        if (!secp->fileline()->warnIsOff(V3ErrorCode::MULTITOP)) {
            secp->v3warn(MULTITOP, "Multiple top level modules\n"
                         <<secp->warnMore()
                         <<"... Suggest see manual; fix the duplicates, or use --top-module to select top."
                         <<V3Error::warnContextNone());
            for (ModVec::const_iterator it = tops.begin(); it != tops.end(); ++it) {
                AstNode* alsop = *it;
                std::cout<<secp->warnMore()<<"... Top module "<<alsop->prettyNameQ()<<endl
                         <<alsop->warnContextSecondary();
            }
        }
    }

    // Reorder the netlist's modules to have modules in level sorted order
    stable_sort(mods.begin(), mods.end(), CmpLevel());  // Sort the vector
    UINFO(9,"modSortByLevel() sorted\n");  // Comment required for gcc4.6.3 / bug666
    for (ModVec::iterator it = mods.begin(); it != mods.end(); ++it) {
        AstNodeModule* nodep = *it;
        nodep->clearIter();  // Because we didn't iterate to find the node
        // pointers, may have a stale m_iterp() needing cleanup
        nodep->unlinkFrBack();
    }
    UASSERT_OBJ(!v3Global.rootp()->modulesp(), v3Global.rootp(), "Unlink didn't work");
    for (ModVec::iterator it = mods.begin(); it != mods.end(); ++it) {
        AstNodeModule* nodep = *it;
        v3Global.rootp()->addModulep(nodep);
    }
    UINFO(9,"modSortByLevel() done\n");  // Comment required for gcc4.6.3 / bug666
    V3Global::dumpCheckGlobalTree("cells", false, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

//######################################################################
// Wrapping

void V3LinkLevel::wrapTop(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // We do ONLY the top module
    AstNodeModule* oldmodp = rootp->modulesp();
    if (!oldmodp) {  // Later V3LinkDot will warn
        UINFO(1,"No module found to wrap\n");
        return;
    }
    AstNodeModule* newmodp = new AstModule(oldmodp->fileline(), string("TOP"));
    // Make the new module first in the list
    oldmodp->unlinkFrBackWithNext();
    newmodp->addNext(oldmodp);
    newmodp->level(1);
    newmodp->modPublic(true);
    newmodp->protect(false);
    rootp->addModulep(newmodp);

    // TODO the module creation above could be done after linkcells, but
    // the rest must be done after data type resolution
    wrapTopCell(rootp);

    // Instantiate all packages under the top wrapper
    // This way all later SCOPE based optimizations can ignore packages
    for (AstNodeModule* modp = rootp->modulesp(); modp; modp=VN_CAST(modp->nextp(), NodeModule)) {
        if (VN_IS(modp, Package)) {
            AstCell* cellp = new AstCell(modp->fileline(),
                                         modp->fileline(),
                                         // Could add __03a__03a="::" to prevent conflict
                                         // with module names/"v"
                                         modp->name(),
                                         modp->name(),
                                         NULL, NULL, NULL);
            cellp->modp(modp);
            newmodp->addStmtp(cellp);
        }
    }

    V3Global::dumpCheckGlobalTree("wraptop", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}

void V3LinkLevel::wrapTopCell(AstNetlist* rootp) {
    AstNodeModule* newmodp = rootp->modulesp();
    UASSERT_OBJ(newmodp && newmodp->isTop(), rootp, "No TOP module found to insert under");

    // Find all duplicate signal names (if multitop)
    typedef vl_unordered_set<std::string> NameSet;
    NameSet ioNames;
    NameSet dupNames;
    // For all modules, skipping over new top
    for (AstNodeModule* oldmodp = VN_CAST(rootp->modulesp()->nextp(), NodeModule);
         oldmodp && oldmodp->level() <= 2;
         oldmodp = VN_CAST(oldmodp->nextp(), NodeModule)) {
        for (AstNode* subnodep = oldmodp->stmtsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* oldvarp = VN_CAST(subnodep, Var)) {
                if (oldvarp->isIO()) {
                    if (ioNames.find(oldvarp->name()) != ioNames.end()) {
                        //UINFO(8, "Multitop dup I/O found: "<<oldvarp<<endl);
                        dupNames.insert(oldvarp->name());
                    } else {
                        ioNames.insert(oldvarp->name());
                    }
                }
            }
        }
    }

    // For all modules, skipping over new top
    for (AstNodeModule* oldmodp = VN_CAST(rootp->modulesp()->nextp(), NodeModule);
         oldmodp && oldmodp->level() <= 2;
         oldmodp = VN_CAST(oldmodp->nextp(), NodeModule)) {
        if (VN_IS(oldmodp, Package)) continue;
        // Add instance
        UINFO(5,"LOOP "<<oldmodp<<endl);
        AstCell* cellp = new AstCell(newmodp->fileline(),
                                     newmodp->fileline(),
                                     (!v3Global.opt.l2Name().empty()
                                      ? v3Global.opt.l2Name() : oldmodp->name()),
                                     oldmodp->name(),
                                     NULL, NULL, NULL);
        cellp->modp(oldmodp);
        newmodp->addStmtp(cellp);

        // Add pins
        for (AstNode* subnodep=oldmodp->stmtsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* oldvarp = VN_CAST(subnodep, Var)) {
                UINFO(8,"VARWRAP "<<oldvarp<<endl);
                if (oldvarp->isIO()) {
                    string name = oldvarp->name();
                    if (dupNames.find(name) != dupNames.end()) {
                        // __02E=. while __DOT__ looks nicer but will break V3LinkDot
                        name = oldmodp->name()+"__02E"+name;
                    }

                    AstVar* varp = oldvarp->cloneTree(false);
                    varp->name(name);
                    varp->protect(false);
                    newmodp->addStmtp(varp);
                    varp->sigPublic(true);  // User needs to be able to get to it...
                    if (oldvarp->isIO()) {
                        oldvarp->primaryIO(false);
                        varp->primaryIO(true);
                    }
                    if (varp->direction().isRefOrConstRef()) {
                        varp->v3error("Unsupported: ref/const ref as primary input/output: "
                                      <<varp->prettyNameQ());
                    }
                    if (varp->isIO() && v3Global.opt.systemC()) {
                        varp->sc(true);
                        // User can see trace one level down from the wrapper
                        // Avoids packing & unpacking SC signals a second time
                        varp->trace(false);
                    }

                    AstPin* pinp = new AstPin(oldvarp->fileline(), 0, varp->name(),
                                              new AstVarRef(varp->fileline(),
                                                            varp, oldvarp->isWritable()));
                    // Skip length and width comp; we know it's a direct assignment
                    pinp->modVarp(oldvarp);
                    cellp->addPinsp(pinp);
                }
            }
        }
    }
}
