// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkLevel.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Levelizing class functions

struct CmpLevel {
    bool operator()(const AstNodeModule* lhsp, const AstNodeModule* rhsp) const {
        return lhsp->level() < rhsp->level();
    }
};

void V3LinkLevel::modSortByLevel() {
    // Sort modules by levels, root down to lowest children
    // Calculate levels again in case we added modules
    UINFO(2, "modSortByLevel()\n");

    // level() was computed for us in V3LinkCells

    ModVec mods;  // Modules
    ModVec tops;  // Top level modules
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_AS(nodep->nextp(), NodeModule)) {
        if (nodep->level() <= 2 && !VN_IS(nodep, NotFoundModule)) tops.push_back(nodep);
        mods.push_back(nodep);
    }
    if (tops.size() >= 2) {
        const AstNode* const secp = tops[1];  // Complain about second one, as first often intended
        if (!secp->fileline()->warnIsOff(V3ErrorCode::MULTITOP)) {
            auto warnTopModules = [](const std::string& warnMore, ModVec tops)
                                      VL_REQUIRES(V3Error::s().m_mutex) -> std::string {
                std::stringstream ss;
                for (AstNode* alsop : tops) {
                    ss << warnMore << "... Top module " << alsop->prettyNameQ() << endl
                       << alsop->warnContextSecondary();
                }
                return ss.str();
            };

            secp->v3warn(MULTITOP, "Multiple top level modules\n"
                                       << secp->warnMore()
                                       << "... Suggest see manual; fix the duplicates, or use "
                                          "--top-module to select top."
                                       << V3Error::s().warnContextNone()
                                       << V3Error::warnAdditionalInfo()
                                       << warnTopModules(secp->warnMore(), tops));
        }
    }

    timescaling(mods);

    // Reorder the netlist's modules to have modules in level sorted order
    stable_sort(mods.begin(), mods.end(), CmpLevel());  // Sort the vector
    UINFO(9, "modSortByLevel() sorted\n");  // Comment required for gcc4.6.3 / bug666
    for (AstNodeModule* nodep : mods) nodep->unlinkFrBack();
    UASSERT_OBJ(!v3Global.rootp()->modulesp(), v3Global.rootp(), "Unlink didn't work");
    for (AstNodeModule* nodep : mods) v3Global.rootp()->addModulesp(nodep);
    UINFO(9, "modSortByLevel() done\n");  // Comment required for gcc4.6.3 / bug666
    V3Global::dumpCheckGlobalTree("cells", false, dumpTreeLevel() >= 3);
}

void V3LinkLevel::timescaling(const ModVec& mods) {
    // Timescale determination
    const AstNodeModule* modTimedp = nullptr;
    VTimescale unit(VTimescale::NONE);
    // Use highest level module as default unit - already sorted in proper order
    for (const auto& modp : mods) {
        if (!modTimedp && !modp->timeunit().isNone()) {
            modTimedp = modp;
            unit = modTimedp->timeunit();
            break;
        }
    }
    unit = v3Global.opt.timeComputeUnit(unit);  // Apply override
    if (unit.isNone()) unit = VTimescale{VTimescale::TS_DEFAULT};
    v3Global.rootp()->timeunit(unit);

    bool dunitTimed = false;  // $unit had a timeunit
    if (const AstPackage* const upkgp = v3Global.rootp()->dollarUnitPkgp()) {
        if (!upkgp->timeunit().isNone()) dunitTimed = true;
    }

    for (AstNodeModule* nodep : mods) {
        if (!v3Global.opt.timeOverrideUnit().isNone()) nodep->timeunit(unit);
        if (nodep->timeunit().isNone()) {
            if (modTimedp  // Got previous
                && !dunitTimed
                && (  // unit doesn't already include an override
                    v3Global.opt.timeOverrideUnit().isNone()
                    && v3Global.opt.timeDefaultUnit().isNone())
                && nodep->timescaleMatters()) {
                nodep->v3warn(TIMESCALEMOD,
                              "Timescale missing on this module as other modules have "
                              "it (IEEE 1800-2017 3.14.2.3)\n"
                                  << nodep->warnContextPrimary() << '\n'
                                  << modTimedp->warnOther()
                                  << "... Location of module with timescale\n"
                                  << modTimedp->warnContextSecondary());
            }
            nodep->timeunit(unit);
        }
    }

    v3Global.rootp()->timescaleSpecified(modTimedp);  // true if some module specifies timescale

    if (v3Global.rootp()->timeprecision().isNone()) {
        v3Global.rootp()->timeprecisionMerge(v3Global.rootp()->fileline(),
                                             VTimescale{VTimescale::TS_DEFAULT});
    }

    // Classes under package have timescale propagated in V3LinkParse
}

//######################################################################
// Wrapping

void V3LinkLevel::wrapTop(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // We do ONLY the top module
    AstNodeModule* const oldmodp = rootp->modulesp();
    if (!oldmodp) {  // Later V3LinkDot will warn
        UINFO(1, "No module found to wrap\n");
        return;
    }

    AstNodeModule* const newmodp = new AstModule{oldmodp->fileline(), "$root"};
    newmodp->name(AstNode::encodeName(newmodp->name()));  // so origName is nice
    // Make the new module first in the list
    oldmodp->unlinkFrBackWithNext();
    newmodp->addNext(oldmodp);
    newmodp->level(1);
    newmodp->modPublic(true);
    newmodp->protect(false);
    newmodp->timeunit(oldmodp->timeunit());
    rootp->addModulesp(newmodp);

    // TODO the module creation above could be done after linkcells, but
    // the rest must be done after data type resolution
    wrapTopCell(rootp);

    // Instantiate all packages under the top wrapper
    // This way all later SCOPE based optimizations can ignore packages
    for (AstNodeModule* modp = rootp->modulesp(); modp; modp = VN_AS(modp->nextp(), NodeModule)) {
        if (VN_IS(modp, Package)) {
            AstCell* const cellp
                = new AstCell{modp->fileline(), modp->fileline(),
                              // Could add __03a__03a="::" to prevent conflict
                              // with module names/"v"
                              modp->name(), modp->name(), nullptr, nullptr, nullptr};
            cellp->modp(modp);
            newmodp->addStmtsp(cellp);
        }
    }

    V3Global::dumpCheckGlobalTree("wraptop", 0, dumpTreeLevel() >= 6);
}

void V3LinkLevel::wrapTopCell(AstNetlist* rootp) {
    AstNodeModule* const newmodp = rootp->modulesp();
    UASSERT_OBJ(newmodp && newmodp->isTop(), rootp, "No TOP module found to insert under");

    // Find all duplicate signal names (if multitop)
    using NameSet = std::unordered_set<std::string>;
    NameSet ioNames;
    NameSet dupNames;
    // For all modules, skipping over new top
    for (AstNodeModule* oldmodp = VN_AS(rootp->modulesp()->nextp(), NodeModule);
         oldmodp && oldmodp->level() <= 2; oldmodp = VN_AS(oldmodp->nextp(), NodeModule)) {
        for (AstNode* subnodep = oldmodp->stmtsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* const oldvarp = VN_CAST(subnodep, Var)) {
                if (oldvarp->isIO()) {
                    if (ioNames.find(oldvarp->name()) != ioNames.end()) {
                        // UINFO(8, "Multitop dup I/O found: " << oldvarp << endl);
                        dupNames.insert(oldvarp->name());
                    } else {
                        ioNames.insert(oldvarp->name());
                    }
                } else if (v3Global.opt.topIfacesSupported() && oldvarp->isIfaceRef()) {
                    const AstNodeDType* const subtypep = oldvarp->subDTypep();
                    if (VN_IS(subtypep, IfaceRefDType)) {
                        const AstIfaceRefDType* const ifacerefp = VN_AS(subtypep, IfaceRefDType);
                        if (!ifacerefp->cellp()) {
                            if (ioNames.find(oldvarp->name()) != ioNames.end()) {
                                // UINFO(8, "Multitop dup interface found: " << oldvarp << endl);
                                dupNames.insert(oldvarp->name());
                            } else {
                                ioNames.insert(oldvarp->name());
                            }
                        }
                    }
                    if (VN_IS(subtypep, UnpackArrayDType)) {
                        const AstUnpackArrayDType* const arrp = VN_AS(subtypep, UnpackArrayDType);
                        const AstNodeDType* const arrsubtypep = arrp->subDTypep();
                        if (VN_IS(arrsubtypep, IfaceRefDType)) {
                            const AstIfaceRefDType* const ifacerefp
                                = VN_AS(arrsubtypep, IfaceRefDType);
                            if (!ifacerefp->cellp()) {
                                if (ioNames.find(oldvarp->name()) != ioNames.end()) {
                                    // UINFO(8, "Multitop dup interface array found: " << oldvarp
                                    // << endl);
                                    dupNames.insert(oldvarp->name());
                                } else {
                                    ioNames.insert(oldvarp->name());
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // For all modules, skipping over new top
    for (AstNodeModule* oldmodp = VN_AS(rootp->modulesp()->nextp(), NodeModule);
         oldmodp && oldmodp->level() <= 2; oldmodp = VN_AS(oldmodp->nextp(), NodeModule)) {
        if (VN_IS(oldmodp, Package)) continue;
        // Add instance
        UINFO(5, "LOOP " << oldmodp << endl);
        AstCell* const cellp = new AstCell{
            newmodp->fileline(),
            newmodp->fileline(),
            (!v3Global.opt.l2Name().empty() ? v3Global.opt.l2Name() : oldmodp->name()),
            oldmodp->name(),
            nullptr,
            nullptr,
            nullptr};
        cellp->modp(oldmodp);
        newmodp->addStmtsp(cellp);

        // Add pins
        for (AstNode* subnodep = oldmodp->stmtsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* const oldvarp = VN_CAST(subnodep, Var)) {
                UINFO(8, "VARWRAP " << oldvarp << endl);
                if (oldvarp->isIO()) {
                    string name = oldvarp->name();
                    if (dupNames.find(name) != dupNames.end()) {
                        // __02E=. while __DOT__ looks nicer but will break V3LinkDot
                        name = oldmodp->name() + "__02E" + name;
                    }

                    AstVar* const varp = oldvarp->cloneTree(false);
                    varp->name(name);
                    varp->protect(false);
                    newmodp->addStmtsp(varp);
                    varp->sigPublic(true);  // User needs to be able to get to it...
                    oldvarp->primaryIO(false);
                    varp->primaryIO(true);
                    if (varp->isRef() || varp->isConstRef()) {
                        varp->v3warn(E_UNSUPPORTED,
                                     "Unsupported: ref/const ref as primary input/output: "
                                         << varp->prettyNameQ());
                    }
                    if (varp->isIO() && v3Global.opt.systemC()) {
                        varp->sc(true);
                        // User can see trace one level down from the wrapper
                        // Avoids packing & unpacking SC signals a second time
                        varp->trace(false);
                    }

                    if (v3Global.opt.noTraceTop() && varp->isIO()) { varp->trace(false); }

                    AstPin* const pinp = new AstPin{
                        oldvarp->fileline(), 0, varp->name(),
                        new AstVarRef{varp->fileline(), varp,
                                      oldvarp->isWritable() ? VAccess::WRITE : VAccess::READ}};
                    // Skip length and width comp; we know it's a direct assignment
                    pinp->modVarp(oldvarp);
                    cellp->addPinsp(pinp);
                } else if (v3Global.opt.topIfacesSupported() && oldvarp->isIfaceRef()) {
                    // for each interface port on oldmodp instantiate a corresponding interface
                    // cell in $root
                    const AstNodeDType* const subtypep = oldvarp->subDTypep();
                    if (VN_IS(subtypep, IfaceRefDType)) {
                        const AstIfaceRefDType* const ifacerefp = VN_AS(subtypep, IfaceRefDType);
                        if (!ifacerefp->cellp()) {
                            string name = oldvarp->name();
                            if (dupNames.find(name) != dupNames.end()) {
                                // __02E=. while __DOT__ looks nicer but will break V3LinkDot
                                name = oldmodp->name() + "__02E" + name;
                            }

                            AstCell* ifacecellp = new AstCell{newmodp->fileline(),
                                                              newmodp->fileline(),
                                                              name,
                                                              ifacerefp->ifaceName(),
                                                              nullptr,
                                                              nullptr,
                                                              nullptr};
                            ifacecellp->modp(ifacerefp->ifacep());
                            newmodp->addStmtsp(ifacecellp);

                            AstIfaceRefDType* const idtypep = new AstIfaceRefDType{
                                newmodp->fileline(), name, ifacerefp->ifaceName()};
                            idtypep->ifacep(nullptr);
                            idtypep->dtypep(idtypep);
                            idtypep->cellp(ifacecellp);
                            rootp->typeTablep()->addTypesp(idtypep);

                            AstVar* varp = new AstVar{newmodp->fileline(), VVarType::IFACEREF,
                                                      name + "__Viftop", idtypep};
                            varp->isIfaceParent(true);
                            ifacecellp->addNextHere(varp);
                            ifacecellp->hasIfaceVar(true);

                            AstPin* const pinp
                                = new AstPin{oldvarp->fileline(), 0, varp->name(),
                                             new AstVarRef{varp->fileline(), varp,
                                                           oldvarp->isWritable() ? VAccess::WRITE
                                                                                 : VAccess::READ}};
                            pinp->modVarp(oldvarp);
                            cellp->addPinsp(pinp);
                        }
                    } else if (VN_IS(subtypep, UnpackArrayDType)) {
                        const AstUnpackArrayDType* const oldarrp
                            = VN_AS(subtypep, UnpackArrayDType);
                        const AstNodeDType* const arrsubtypep = oldarrp->subDTypep();
                        if (VN_IS(arrsubtypep, IfaceRefDType)) {
                            const AstIfaceRefDType* const ifacerefp
                                = VN_AS(arrsubtypep, IfaceRefDType);
                            if (!ifacerefp->cellp()) {
                                string name = oldvarp->name();
                                if (dupNames.find(name) != dupNames.end()) {
                                    // __02E=. while __DOT__ looks nicer but will break V3LinkDot
                                    name = oldmodp->name() + "__02E" + name;
                                }

                                AstUnpackArrayDType* arraydtypep
                                    = VN_AS(oldvarp->dtypep(), UnpackArrayDType);
                                AstCell* ifacearraycellp
                                    = new AstCell{newmodp->fileline(),
                                                  newmodp->fileline(),
                                                  name,
                                                  ifacerefp->ifaceName(),
                                                  nullptr,
                                                  nullptr,
                                                  arraydtypep->rangep()->cloneTree(true)};
                                ifacearraycellp->modp(ifacerefp->ifacep());
                                newmodp->addStmtsp(ifacearraycellp);

                                AstIfaceRefDType* const idtypep = new AstIfaceRefDType{
                                    newmodp->fileline(), name, ifacerefp->ifaceName()};
                                idtypep->ifacep(nullptr);
                                idtypep->dtypep(idtypep);
                                idtypep->cellp(ifacearraycellp);
                                rootp->typeTablep()->addTypesp(idtypep);

                                AstNodeArrayDType* const arrp = new AstUnpackArrayDType{
                                    newmodp->fileline(), idtypep,
                                    arraydtypep->rangep()->cloneTree(true)};
                                AstVar* varp = new AstVar{newmodp->fileline(), VVarType::IFACEREF,
                                                          name + "__Viftop", arrp};
                                varp->isIfaceParent(true);
                                ifacearraycellp->addNextHere(varp);
                                ifacearraycellp->hasIfaceVar(true);
                                rootp->typeTablep()->addTypesp(arrp);

                                AstPin* const pinp = new AstPin{
                                    oldvarp->fileline(), 0, varp->name(),
                                    new AstVarRef{varp->fileline(), varp,
                                                  oldvarp->isWritable() ? VAccess::WRITE
                                                                        : VAccess::READ}};
                                pinp->modVarp(oldvarp);
                                cellp->addPinsp(pinp);
                            }
                        }
                    }
                }
            }
        }
    }
}
