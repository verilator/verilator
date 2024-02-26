// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCConstInit.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <cstdint>
#include <set>
#include <string>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Internal EmitC implementation

class EmitCHeader final : public EmitCConstInit {
    V3UniqueNames m_names;
    // METHODS

    void decorateFirst(bool& first, const string& str) {
        if (first) {
            putsDecoration(nullptr, str);
            first = false;
        }
    }
    void emitCellDecls(const AstNodeModule* modp) {
        bool first = true;
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                decorateFirst(first, "// CELLS\n");
                putns(cellp,
                      prefixNameProtect(cellp->modp()) + "* " + cellp->nameProtect() + ";\n");
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
        if (const AstClass* const classp = VN_CAST(modp, Class)) {
            if (classp->needRNG()) {
                putsDecoration(nullptr, "\n// INTERNAL VARIABLES\n");
                puts("VlRNG __Vm_rng;\n");
            }
        } else {  // not class
            putsDecoration(nullptr, "\n// INTERNAL VARIABLES\n");
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
                    putns(varp, "static ");
                    puts(canBeConstexpr ? "constexpr " : "const ");
                    puts(varp->dtypep()->cType(varp->nameProtect(), false, false));
                    if (canBeConstexpr) {
                        puts(" = ");
                        iterateConst(varp->valuep());
                    }
                    puts(";\n");
                }
            }
        }
    }
    void emitCtorDtorDecls(const AstNodeModule* modp) {
        if (!VN_IS(modp, Class)) {  // Classes use CFuncs with isConstructor/isDestructor
            const string& name = prefixNameProtect(modp);
            putsDecoration(nullptr, "\n// CONSTRUCTORS\n");
            putns(modp, name + "(" + symClassName() + "* symsp, const char* v__name);\n");
            putns(modp, "~" + name + "();\n");
            putns(modp, "VL_UNCOPYABLE(" + name + ");\n");
        }
    }
    void emitInternalMethodDecls(const AstNodeModule* modp) {
        bool first = true;
        const string section = "\n// INTERNAL METHODS\n";

        if (!VN_IS(modp, Class)) {
            decorateFirst(first, section);
            puts("void " + protect("__Vconfigure") + "(bool first);\n");
        }

        if (v3Global.opt.coverage() && !VN_IS(modp, Class)) {
            decorateFirst(first, section);
            puts("void __vlCoverInsert(");
            puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
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
                putsDecoration(tdefp,
                               "// enum " + tdefp->nameProtect() + " ignored: Too wide for C++\n");
            } else {
                putns(tdefp, "enum " + tdefp->name() + " {\n");
                for (const AstEnumItem* itemp = edtypep->itemsp(); itemp;
                     itemp = VN_AS(itemp->nextp(), EnumItem)) {
                    if (const AstConst* const constp = VN_CAST(itemp->valuep(), Const)) {
                        if (constp->num().isFourState()) {
                            putns(itemp, "// " + itemp->nameProtect() + " is four-state\n");
                            continue;
                        }
                    }
                    putns(itemp, itemp->nameProtect());
                    puts(" = ");
                    iterateConst(itemp->valuep());
                    if (VN_IS(itemp->nextp(), EnumItem)) puts(",");
                    puts("\n");
                }
                puts("};\n");
            }
        }
    }
    void emitStructDecl(const AstNodeModule* modp, AstNodeUOrStructDType* sdtypep,
                        std::set<AstNodeUOrStructDType*>& emitted) {
        if (emitted.count(sdtypep) > 0) return;
        emitted.insert(sdtypep);
        for (const AstMemberDType* itemp = sdtypep->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            AstNodeUOrStructDType* const subp = itemp->getChildStructp();
            if (subp && (!subp->packed() || sdtypep->packed())) {
                // Recurse if it belongs to the current module
                if (subp->classOrPackagep() == modp) {
                    emitStructDecl(modp, subp, emitted);
                    puts("\n");
                }
            }
        }
        if (sdtypep->packed()) {
            emitPackedUOrSBody(sdtypep);
        } else {
            emitUnpackedUOrSBody(sdtypep);
        }
    }
    void emitUnpackedUOrSBody(AstNodeUOrStructDType* sdtypep) {
        putns(sdtypep, sdtypep->verilogKwd());  // "struct"/"union"
        puts(" " + EmitCBase::prefixNameProtect(sdtypep) + " {\n");
        for (const AstMemberDType* itemp = sdtypep->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            putns(itemp, itemp->dtypep()->cType(itemp->nameProtect(), false, false));
            puts(";\n");
        }

        putns(sdtypep, "\nbool operator==(const " + EmitCBase::prefixNameProtect(sdtypep)
                           + "& rhs) const {\n");
        puts("return ");
        for (const AstMemberDType* itemp = sdtypep->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            if (itemp != sdtypep->membersp()) puts("\n    && ");
            putns(itemp, itemp->nameProtect() + " == " + "rhs." + itemp->nameProtect());
        }
        puts(";\n");
        puts("}\n");
        putns(sdtypep, "bool operator!=(const " + EmitCBase::prefixNameProtect(sdtypep)
                           + "& rhs) const {\n");
        puts("return !(*this == rhs);\n}\n");
        puts("};\n");
    }

    // getfunc: VL_ASSIGNSEL_XX(rbits, obits, off, lhsdata, rhsdata);
    // !getfunc: VL_SELASSIGN_XX(rbits, obits, lhsdata, rhsdata, off);
    void emitVlAssign(const AstNodeDType* const lhstype, const AstNodeDType* rhstype,
                      const std::string& off, const std::string& lhsdata,
                      const std::string& rhsdata, bool getfunc) {
        puts(getfunc ? "VL_ASSIGNSEL_" : "VL_SELASSIGN_");
        puts(lhstype->charIQWN());
        puts(rhstype->charIQWN());
        puts("(" + std::to_string(lhstype->width()) + ", ");  // LHS width
        if (getfunc) {
            puts(std::to_string(rhstype->width()) + ", ");  // Number of copy bits
            puts(off + ", ");  // LHS offset
        } else {
            // Number of copy bits. Use widthTototalBytes to
            // make VL_SELASSIGN_XX clear upper unused bits for us.
            // puts(std::to_string(lhstype->width()) + ", ");
            puts(std::to_string(lhstype->widthTotalBytes() * 8) + ", ");
        }
        puts(lhsdata + ", ");  // LHS data
        puts(rhsdata);  // RHS data
        if (!getfunc) {
            puts(", " + off);  // RHS offset
        }
        puts(");\n");
    }

    // `retOrArg` should be prefixed by `&` or suffixed by `.data()` depending on its type
    void emitPackedMember(const AstNodeDType* parentDtypep, const AstNodeDType* dtypep,
                          const std::string& fieldname, const std::string& offset, bool getfunc,
                          const std::string& retOrArg) {
        dtypep = dtypep->skipRefp();
        if (const auto* adtypep = VN_CAST(dtypep, PackArrayDType)) {
            const std::string index = m_names.get("__Vi");
            puts("for (int " + index + " = 0; " + index + " < "
                 + std::to_string(adtypep->elementsConst()) + "; ++" + index + ") {\n");

            const std::string offsetInLoop
                = offset + " + " + index + " * " + std::to_string(adtypep->subDTypep()->width());
            const std::string newName = fieldname + "[" + index + "]";
            emitPackedMember(parentDtypep, adtypep->subDTypep(), newName, offsetInLoop, getfunc,
                             retOrArg);
            puts("}\n");
        } else if (VN_IS(dtypep, NodeUOrStructDType)) {
            const std::string tmp = m_names.get("__Vtmp");
            const std::string suffixName = dtypep->isWide() ? tmp + ".data()" : tmp;
            if (getfunc) {  // Emit `get` func;
                // auto __tmp = field.get();
                puts("auto " + tmp + " = " + fieldname + ".get();\n");
                // VL_ASSIGNSEL_XX(rbits, obits, lsb, lhsdata, rhsdata);
                emitVlAssign(parentDtypep, dtypep, offset, retOrArg, suffixName, getfunc);
            } else {  // Emit `set` func
                const std::string tmptype = AstCDType::typeToHold(dtypep->width());
                // type tmp;
                puts(tmptype + " " + tmp + ";\n");
                // VL_SELASSIGN_XX(rbits, obits, lhsdata, rhsdata, roffset);
                emitVlAssign(dtypep, parentDtypep, offset, suffixName, retOrArg, getfunc);
                // field.set(__tmp);
                puts(fieldname + ".set(" + tmp + ");\n");
            }
        } else {
            UASSERT_OBJ(VN_IS(dtypep, EnumDType) || VN_IS(dtypep, BasicDType), dtypep,
                        "Unsupported type in packed struct or union");
            const std::string suffixName = dtypep->isWide() ? fieldname + ".data()" : fieldname;
            if (getfunc) {  // Emit `get` func;
                // VL_ASSIGNSEL_XX(rbits, obits, lsb, lhsdata, rhsdata);
                emitVlAssign(parentDtypep, dtypep, offset, retOrArg, suffixName, getfunc);
            } else {  // Emit `set` func
                // VL_SELASSIGN_XX(rbits, obits, lhsdata, rhsdata, roffset);
                emitVlAssign(dtypep, parentDtypep, offset, suffixName, retOrArg, getfunc);
            }
        }
    }
    void emitPackedUOrSBody(AstNodeUOrStructDType* sdtypep) {
        putns(sdtypep, sdtypep->verilogKwd());  // "struct"/"union"
        puts(" " + EmitCBase::prefixNameProtect(sdtypep) + " {\n");

        AstMemberDType* itemp;
        AstMemberDType* lastItemp;
        AstMemberDType* witemp = nullptr;
        // LSB is first field in C, so loop backwards
        for (lastItemp = sdtypep->membersp(); lastItemp && lastItemp->nextp();
             lastItemp = VN_AS(lastItemp->nextp(), MemberDType)) {
            if (lastItemp->width() == sdtypep->width()) witemp = lastItemp;
        }
        for (itemp = lastItemp; itemp; itemp = VN_CAST(itemp->backp(), MemberDType)) {
            putns(itemp, itemp->dtypep()->cType(itemp->nameProtect(), false, false, true));
            puts(";\n");
        }

        const std::string retArgName = m_names.get("__v");
        const std::string suffixName = sdtypep->isWide() ? retArgName + ".data()" : retArgName;
        const std::string retArgType = AstCDType::typeToHold(sdtypep->width());

        // Emit `get` member function
        puts(retArgType + " get() const {\n");
        puts(retArgType + " " + retArgName + ";\n");
        if (VN_IS(sdtypep, StructDType)) {
            for (itemp = lastItemp; itemp; itemp = VN_CAST(itemp->backp(), MemberDType)) {
                emitPackedMember(sdtypep, itemp->dtypep(), itemp->nameProtect(),
                                 std::to_string(itemp->lsb()), /*getfunc=*/true, suffixName);
            }
        } else {
            // We only need to fill the widest field of union
            emitPackedMember(sdtypep, witemp->dtypep(), witemp->nameProtect(),
                             std::to_string(witemp->lsb()), /*getfunc=*/true, suffixName);
        }
        puts("return " + retArgName + ";\n");
        puts("}\n");

        // Emit `set` member function
        puts("void set(const " + retArgType + "& " + retArgName + ") {\n");
        if (VN_IS(sdtypep, StructDType)) {
            for (itemp = lastItemp; itemp; itemp = VN_CAST(itemp->backp(), MemberDType)) {
                emitPackedMember(sdtypep, itemp->dtypep(), itemp->nameProtect(),
                                 std::to_string(itemp->lsb()), /*getfunc=*/false, suffixName);
            }
        } else {
            // We only need to fill the widest field of union
            emitPackedMember(sdtypep, witemp->dtypep(), witemp->nameProtect(),
                             std::to_string(witemp->lsb()), /*getfunc=*/false, suffixName);
        }

        puts("}\n");

        puts("};\n");
        m_names.reset();
    }
    void emitStructs(const AstNodeModule* modp) {
        // Track structs that've been emitted already
        std::set<AstNodeUOrStructDType*> emitted;
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            const AstTypedef* const tdefp = VN_CAST(nodep, Typedef);
            if (!tdefp) continue;
            AstNodeUOrStructDType* const sdtypep
                = VN_CAST(tdefp->dtypep()->skipRefToEnump(), NodeUOrStructDType);
            if (!sdtypep) continue;
            emitStructDecl(modp, sdtypep, emitted);
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
            for (const AstClassExtends* extp = classp->extendsp(); extp;
                 extp = VN_AS(extp->nextp(), ClassExtends)) {
                putns(extp, "#include \"" + prefixNameProtect(extp->classp()->classOrPackagep())
                                + ".h\"\n");
            }
        }

        // Forward declarations required by this AstNodeModule
        puts("\nclass " + symClassName() + ";\n");

        // From `systemc_header
        emitTextSection(modp, VNType::atScHdr);

        emitStructs(modp);

        // Open class body {{{
        puts("\n");
        putns(modp, "class ");
        if (!VN_IS(modp, Class)) puts("alignas(VL_CACHE_LINE_BYTES) ");
        puts(prefixNameProtect(modp));
        if (const AstClass* const classp = VN_CAST(modp, Class)) {
            const string virtpub = classp->useVirtualPublic() ? "virtual public " : "public ";
            puts(" : " + virtpub);
            if (classp->extendsp()) {
                for (const AstClassExtends* extp = classp->extendsp(); extp;
                     extp = VN_AS(extp->nextp(), ClassExtends)) {
                    putns(extp, prefixNameProtect(extp->classp()));
                    if (extp->nextp()) puts(", " + virtpub);
                }
            } else {
                puts("VlClass");
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
        puts("};\n");
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
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};

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
        if (v3Global.usesTiming()) puts("#include \"verilated_timing.h\"\n");

        std::set<string> cuse_set;
        auto add_to_cuse_set = [&](string s) { cuse_set.insert(s); };

        forModCUse(modp, VUseType::INT_FWD_CLASS | VUseType::INT_INCLUDE, add_to_cuse_set);
        if (const AstClassPackage* const packagep = VN_CAST(modp, ClassPackage)) {
            forModCUse(packagep->classp(), VUseType::INT_INCLUDE | VUseType::INT_FWD_CLASS,
                       add_to_cuse_set);
        }

        for (const string& s : cuse_set) puts(s);
        puts("\n");

        emitAll(modp);

        if (const AstClassPackage* const packagep = VN_CAST(modp, ClassPackage)) {
            // Put the non-static class implementation in same h file for speed
            emitAll(packagep->classp());
        }

        ofp()->putsEndGuard();

        // Close output file
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
    ~EmitCHeader() override = default;

public:
    static void main(const AstNodeModule* modp) { EmitCHeader emitCHeader{modp}; }
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
