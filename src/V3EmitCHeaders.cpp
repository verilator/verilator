// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3EmitC.h"
#include "V3EmitCConstInit.h"
#include "V3Global.h"

#include <algorithm>
#include <vector>

//######################################################################
// Internal EmitC implementation

class EmitCHeader final : public EmitCConstInit {
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void decorateFirst(bool& first, const string& str) {
        if (first) {
            putsDecoration(str);
            first = false;
        }
    }
    void emitCellDecls(const AstNodeModule* modp) {
        bool first = true;
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                decorateFirst(first, "// CELLS\n");
                puts(prefixNameProtect(cellp->modp()) + "* " + cellp->nameProtect() + ";\n");
            }
        }
    }
    void emitDesignVarDecls(const AstNodeModule* modp) {
        bool first = true;
        std::vector<const AstVar*> varList;
        bool lastAnon = false;  // initial value is not important, but is used

        const auto emitCurrentList = [this, &first, &varList, &lastAnon]() {
            if (varList.empty()) return;

            decorateFirst(first, "\n// DESIGN SPECIFIC STATE\n");

            if (lastAnon) {  // Output as anons
                const int anonMembers = varList.size();
                const int lim = v3Global.opt.compLimitMembers();
                int anonL3s = 1;
                int anonL2s = 1;
                int anonL1s = 1;
                if (anonMembers > (lim * lim * lim)) {
                    anonL3s = (anonMembers + (lim * lim * lim) - 1) / (lim * lim * lim);
                    anonL2s = lim;
                    anonL1s = lim;
                } else if (anonMembers > (lim * lim)) {
                    anonL2s = (anonMembers + (lim * lim) - 1) / (lim * lim);
                    anonL1s = lim;
                } else if (anonMembers > lim) {
                    anonL1s = (anonMembers + lim - 1) / lim;
                }
                if (anonL1s != 1)
                    puts("// Anonymous structures to workaround compiler member-count bugs\n");
                auto it = varList.cbegin();
                for (int l3 = 0; l3 < anonL3s && it != varList.cend(); ++l3) {
                    if (anonL3s != 1) puts("struct {\n");
                    for (int l2 = 0; l2 < anonL2s && it != varList.cend(); ++l2) {
                        if (anonL2s != 1) puts("struct {\n");
                        for (int l1 = 0; l1 < anonL1s && it != varList.cend(); ++l1) {
                            if (anonL1s != 1) puts("struct {\n");
                            for (int l0 = 0; l0 < lim && it != varList.cend(); ++l0) {
                                emitVarDecl(*it);
                                ++it;
                            }
                            if (anonL1s != 1) puts("};\n");
                        }
                        if (anonL2s != 1) puts("};\n");
                    }
                    if (anonL3s != 1) puts("};\n");
                }
                // Leftovers, just in case off by one error somewhere above
                for (; it != varList.cend(); ++it) emitVarDecl(*it);
            } else {  // Output as nonanons
                for (const auto& pair : varList) emitVarDecl(pair);
            }

            varList.clear();
        };

        // Emit variables in consecutive anon and non-anon batches
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isIO() || varp->isSignal() || varp->isClassMember() || varp->isTemp()) {
                    const bool anon = isAnonOk(varp);
                    if (anon != lastAnon) emitCurrentList();
                    lastAnon = anon;
                    varList.emplace_back(varp);
                }
            }
        }

        // Emit final batch
        emitCurrentList();
    }
    void emitInternalVarDecls(const AstNodeModule* modp) {
        if (!VN_IS(modp, Class)) {
            putsDecoration("\n// INTERNAL VARIABLES\n");
            puts(symClassName() + "* const vlSymsp;\n");
        }
    }
    void emitParamDecls(const AstNodeModule* modp) {
        bool first = true;
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isParam()) {
                    decorateFirst(first, "\n// PARAMETERS\n");
                    UASSERT_OBJ(varp->valuep(), nodep, "No init for a param?");
                    // Only C++ LiteralTypes can be constexpr
                    const bool canBeConstexpr = varp->dtypep()->isLiteralType();
                    puts("static ");
                    puts(canBeConstexpr ? "constexpr " : "const ");
                    puts(varp->dtypep()->cType(varp->nameProtect(), false, false));
                    if (canBeConstexpr) {
                        puts(" = ");
                        iterate(varp->valuep());
                    }
                    puts(";\n");
                }
            }
        }
    }
    void emitCtorDtorDecls(const AstNodeModule* modp) {
        if (!VN_IS(modp, Class)) {  // Classes use CFuncs with isConstructor/isDestructor
            const string& name = prefixNameProtect(modp);
            putsDecoration("\n// CONSTRUCTORS\n");
            puts(name + "(" + symClassName() + "* symsp, const char* name);\n");
            puts("~" + name + "();\n");
            puts("VL_UNCOPYABLE(" + name + ");\n");
        }
    }
    void emitInternalMethodDecls(const AstNodeModule* modp) {
        bool first = true;
        const string section = "\n// INTERNAL METHODS\n";

        if (!VN_IS(modp, Class)) {
            decorateFirst(first, section);
            puts("void " + protect("__Vconfigure") + "(bool first);\n");
        }

        if (v3Global.opt.coverage()) {
            decorateFirst(first, section);
            puts("void __vlCoverInsert(");
            puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp, const char* "
                 "linescovp);\n");
        }

        if (v3Global.opt.savable()) {
            decorateFirst(first, section);
            puts("void " + protect("__Vserialize") + "(VerilatedSerialize& os);\n");
            puts("void " + protect("__Vdeserialize") + "(VerilatedDeserialize& os);\n");
        }
    }
    void emitEnums(const AstNodeModule* modp) {
        bool first = true;
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            const AstTypedef* const tdefp = VN_CAST(nodep, Typedef);
            if (!tdefp) continue;
            if (!tdefp->attrPublic()) continue;
            const AstEnumDType* const edtypep
                = VN_CAST(tdefp->dtypep()->skipRefToEnump(), EnumDType);
            if (!edtypep) continue;
            decorateFirst(first, "\n// ENUMS (that were declared public)\n");
            if (edtypep->width() > 64) {
                putsDecoration("// enum " + tdefp->nameProtect() + " ignored: Too wide for C++\n");
            } else {
                puts("enum " + tdefp->name() + " {\n");
                for (const AstEnumItem* itemp = edtypep->itemsp(); itemp;
                     itemp = VN_AS(itemp->nextp(), EnumItem)) {
                    if (const AstConst* const constp = VN_CAST(itemp->valuep(), Const)) {
                        if (constp->num().isFourState()) {
                            puts("// " + itemp->nameProtect() + " is four-state\n");
                            continue;
                        }
                    }
                    puts(itemp->nameProtect());
                    puts(" = ");
                    iterate(itemp->valuep());
                    if (VN_IS(itemp->nextp(), EnumItem)) puts(",");
                    puts("\n");
                }
                puts("};\n");
            }
        }
    }
    void emitFuncDecls(const AstNodeModule* modp, bool inClassBody) {
        std::vector<const AstCFunc*> funcsp;

        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCFunc* const funcp = VN_CAST(nodep, CFunc)) {
                if (funcp->dpiImportPrototype())  // Declared in __Dpi.h
                    continue;
                if (funcp->dpiExportDispatcher())  // Declared in __Dpi.h
                    continue;
                if (funcp->isMethod() != inClassBody)  // Only methods go inside class
                    continue;
                if (funcp->isMethod() && funcp->isLoose())  // Loose methods are declared lazily
                    continue;
                funcsp.push_back(funcp);
            }
        }

        std::stable_sort(funcsp.begin(), funcsp.end(), [](const AstNode* ap, const AstNode* bp) {
            return ap->name() < bp->name();
        });

        for (const AstCFunc* const funcp : funcsp) {
            if (inClassBody) ofp()->putsPrivate(funcp->declPrivate());
            emitCFuncDecl(funcp, modp);
        }
    }
    void emitAll(const AstNodeModule* modp) {
        // Include files required by this AstNodeModule
        if (const AstClass* const classp = VN_CAST(modp, Class)) {
            if (classp->extendsp()) {
                puts("#include \""
                     + prefixNameProtect(classp->extendsp()->classp()->classOrPackagep())
                     + ".h\"\n");
            }
        }
        emitModCUse(modp, VUseType::INT_INCLUDE);

        // Forward declarations required by this AstNodeModule
        puts("\nclass " + symClassName() + ";\n");
        emitModCUse(modp, VUseType::INT_FWD_CLASS);

        // From `systemc_header
        emitTextSection(modp, VNType::atScHdr);

        // Open class body {{{
        puts("\nclass ");
        puts(prefixNameProtect(modp));
        if (const AstClass* const classp = VN_CAST(modp, Class)) {
            if (classp->extendsp()) {
                puts(" : public ");
                puts(prefixNameProtect(classp->extendsp()->classp()));
            }
        } else {
            puts(" final : public VerilatedModule");
        }
        puts(" {\n");
        ofp()->resetPrivate();
        ofp()->putsPrivate(false);  // public:

        // Emit all class body contents
        emitCellDecls(modp);
        emitEnums(modp);
        emitDesignVarDecls(modp);
        emitInternalVarDecls(modp);
        emitParamDecls(modp);
        emitCtorDtorDecls(modp);
        emitInternalMethodDecls(modp);
        emitFuncDecls(modp, /* inClassBody: */ true);

        // From `systemc_interface
        emitTextSection(modp, VNType::atScInt);

        // Close class body
        if (!VN_IS(modp, Class)) {
            puts("} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);\n");
        } else {
            puts("};\n");
        }
        // }}}

        // Emit out of class function declarations
        puts("\n");
        emitFuncDecls(modp, /* inClassBody: */ false);
    }

    explicit EmitCHeader(const AstNodeModule* modp) {
        UINFO(5, "  Emitting header for " << prefixNameProtect(modp) << endl);

        // Open output file
        const string filename = v3Global.opt.makeDir() + "/" + prefixNameProtect(modp) + ".h";
        newCFile(filename, /* slow: */ false, /* source: */ false);
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile(filename) : new V3OutCFile(filename);

        ofp()->putsHeader();
        puts("// DESCRIPTION: Verilator output: Design internal header\n");
        puts("// See " + topClassName() + ".h for the primary calling header\n");

        ofp()->putsGuard();

        // Include files
        puts("\n");
        ofp()->putsIntTopInclude();
        puts("#include \"verilated.h\"\n");
        if (v3Global.opt.mtasks()) puts("#include \"verilated_threads.h\"\n");
        if (v3Global.opt.savable()) puts("#include \"verilated_save.h\"\n");
        if (v3Global.opt.coverage()) puts("#include \"verilated_cov.h\"\n");

        emitAll(modp);

        if (const AstClassPackage* const packagep = VN_CAST(modp, ClassPackage)) {
            // Put the non-static class implementation in same h file for speed
            emitAll(packagep->classp());
        }

        ofp()->putsEndGuard();

        // Close output file
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
    virtual ~EmitCHeader() override = default;

public:
    static void main(const AstNodeModule* modp) { EmitCHeader emitCHeader(modp); }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcHeaders() {
    UINFO(2, __FUNCTION__ << ": " << endl);

    // Process each module in turn
    for (const AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Class)) continue;  // Declared with the ClassPackage
        EmitCHeader::main(VN_AS(nodep, NodeModule));
    }
}
