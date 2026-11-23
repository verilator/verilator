// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCFunc.h"
#include "V3ThreadPool.h"
#include "V3UniqueNames.h"
#include "V3VNUserAllocator.h"

#include <algorithm>
#include <map>
#include <set>
#include <tuple>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Internal EmitC implementation

class EmitCImp final : public EmitCFunc {
    // TYPES
    struct CtorDtor final {
        TextStmts m_ctorStmts;  // Statements constructing members in 'ctor'
        TextStmts m_dtorStmts;  // Statements destroying members in 'dtor'
        std::string m_ctorSplitDecl;  // Declaration of sub-function 'ctor' was split into, if any
        std::string m_dtorSplitDecl;  // Declaration of sub-function 'dtor' was split into, if any
    };

    // NODE STATE
    //   AstNodeModule::user1()  -> CtorDtor. Constructor/destructor statements (slow only)
    VNUser1Allocator<AstNodeModule, CtorDtor> m_ctorDtors;

    // MEMBERS
    const std::vector<AstNodeModule*>& m_modps;  // Modules emitted into the same output files
    const bool m_slow;  // Creating __Slow file
    V3UniqueNames m_uniqueNames;  // Generates unique file names
    const std::string m_fileBaseName;  // Base name of the output files

    // METHODS
    void openNextOutputFile(const std::string& fileName) {
        openNewOutputSourceFile(fileName, m_slow, false, "Design implementation internals");
        emitFileHeader();
    }
    void emitFileHeader() {
        puts("// See " + EmitCUtil::topClassName() + ".h for the primary calling header\n");
        puts("\n");
        puts("#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        for (const AstNodeModule* const modp : m_modps) {
            emitSystemCSection(modp, VSystemCSectionType::IMP_HDR);
        }
        // Need to emit new lazy declarations
        m_lazyDecls.reset();
    }

    // Open the first common implementation file, or split it if needed
    void openCommonImpFile() {
        if (!ofp()) {
            openNextOutputFile(m_fileBaseName);
        } else if (splitNeeded()) {
            splitOutputFile();
        }
    }

    void emitParamDefns(const AstNodeModule* modp) {
        bool first = true;
        for (const AstNode* const nodep : modp->stmtspList()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isParam()) {
                    if (first) {
                        openCommonImpFile();
                        puts("\n");
                        const string modName = EmitCUtil::prefixNameProtect(modp);
                        putsDecoration(modp, "// Parameter definitions for " + modName + "\n");
                        first = false;
                    }
                    if (varp->dtypep()->isLiteralType()) putns(varp, "VL_CONSTINIT_CXX20 ");
                    putns(varp, "const ");
                    emitVarDefn(varp);
                    puts(";\n");
                }
            }
        }
        if (!first) puts("\n");
    }
    // Add statements explicitly constructing, or destroying, a member AstVar
    static void addVarCtorDtorStmts(TextStmts& stmts, const AstVar* varp, bool destroy) {
        const std::string name = "vlSelf->" + varName(varp);

        // SystemC port arrays are C arrays, so construct them element by element. They are
        // default constructed (unnamed), as the elements of an array member would be.
        if (varp->isSc() && VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) {
            std::vector<std::string> elems{name};
            for (const AstUnpackArrayDType* adtypep
                 = VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType);
                 adtypep; adtypep = VN_CAST(adtypep->subDTypep()->skipRefp(), UnpackArrayDType)) {
                std::vector<std::string> subElems;
                for (const std::string& elem : elems) {
                    for (int i = 0; i < adtypep->elementsConst(); ++i) {
                        subElems.push_back(elem + "[" + std::to_string(i) + "]");
                    }
                }
                elems = std::move(subElems);
            }
            if (destroy) std::reverse(elems.begin(), elems.end());
            for (const std::string& e : elems) {
                stmts.add((destroy ? "VL_INPLACE_DESTRUCT(" : "VL_INPLACE_CONSTRUCT(") + e + ");");
            }
            return;
        }

        // Other variables are constructed whole, even if aggregates
        if (destroy) {
            stmts.add("VL_INPLACE_DESTRUCT(" + name + ");");
            return;
        }
        const AstBasicDType* const basicp = VN_CAST(varp->dtypeSkipRefp(), BasicDType);
        std::string args;
        if (varp->isSc()) {
            // SystemC ports need their name
            args = ", \"" + V3OutFormatter::quoteNameControls(varp->nameProtect()) + "\"";
        } else if (basicp && basicp->isDelayScheduler()) {
            // Delay scheduler needs the context pointer
            args = ", *vlSelf->vlSymsp->_vm_contextp__";
        }
        stmts.add("VL_INPLACE_CONSTRUCT(" + name + args + ");");
    }
    // Gather the statements constructing/destroying members in anonymous unions, and split
    // them into sub-functions if needed. As this emits files, no output file can be open.
    void createCtorDtorStmts(AstNodeModule* modp) {
        CtorDtor& ctorDtor = m_ctorDtors(modp);

        // Construct member variables
        for (const AstNode* const nodep : modp->stmtspList()) {
            const AstVar* const varp = VN_CAST(nodep, Var);
            if (varp && isExplicitlyConstructed(varp)) {
                addVarCtorDtorStmts(ctorDtor.m_ctorStmts, varp, false);
            }
        }

        // Destroy in reverse order
        const AstNode* const lastp = modp->stmtsp() ? modp->stmtsp()->lastp() : nullptr;
        for (const AstNode* nodep = lastp; nodep; nodep = nodep->prevp()) {
            const AstVar* const varp = VN_CAST(nodep, Var);
            if (varp && isExplicitlyConstructed(varp)) {
                addVarCtorDtorStmts(ctorDtor.m_dtorStmts, varp, true);
            }
        }

        // Split into sub-functions if needed
        const std::string modName = EmitCUtil::prefixNameProtect(modp);
        std::tie(ctorDtor.m_ctorSplitDecl, ctorDtor.m_dtorSplitDecl) = emitSplitCtorDtor(
            ctorDtor.m_ctorStmts, ctorDtor.m_dtorStmts, 0, modName, modName + "* vlSelf", "vlSelf",
            false, "Design implementation internals", [this]() { emitFileHeader(); });
    }
    void emitCtorDtorImp(const AstNodeModule* modp) {
        const std::string modName = EmitCUtil::prefixNameProtect(modp);
        const CtorDtor& ctorDtor = m_ctorDtors(modp);
        openCommonImpFile();
        // Cost of the 'ctor'/'dtor' functions and their C++ wrappers, plus the statements below
        splitSizeInc(4 * AstNode::INSTR_COUNT_CTOR_DTOR);

        // ctor
        if (modp->ctorVarReset()) {
            m_lazyDecls.emit("\nvoid " + modName + "__", protect("_ctor_var_reset"),
                             "(" + modName + "* vlSelf);\n");
        }

        if (!ctorDtor.m_ctorSplitDecl.empty()) puts("\n" + ctorDtor.m_ctorSplitDecl + "\n");
        puts("\nvoid " + modName + "__ctor(" + modName + "* vlSelf, " + EmitCUtil::symClassName()
             + "* symsp, const char* namep) {\n");
        puts("vlSelf->vlSymsp = symsp;\n");
        puts("vlSelf->vlNamep = strdup(namep);\n");
        putsDecoration(modp, "// Construct members\n");
        for (const TextStmts::Stmt& stmt : ctorDtor.m_ctorStmts) {
            puts(stmt.m_text + "\n");
            splitSizeInc(stmt.m_cost);
        }

        putsDecoration(modp, "// Reset structure values\n");
        if (modp->ctorVarReset()) {
            puts(modName + "__" + protect("_ctor_var_reset") + "(vlSelf);\n");
        }
        puts("}\n");

        // C++ constructor
        puts("\n" + modName + "::" + modName + "(" + EmitCUtil::symClassName()
             + "* symsp, const char* namep) {\n");
        puts(modName + "__ctor(this, symsp, namep);\n");
        emitSystemCSection(modp, VSystemCSectionType::CTOR);
        puts("}\n");

        // dtor
        if (!ctorDtor.m_dtorSplitDecl.empty()) puts("\n" + ctorDtor.m_dtorSplitDecl + "\n");
        puts("\nvoid " + modName + "__dtor(" + modName + "* vlSelf) {\n");
        putsDecoration(modp, "// Destroy members\n");
        for (const TextStmts::Stmt& stmt : ctorDtor.m_dtorStmts) {
            puts(stmt.m_text + "\n");
            splitSizeInc(stmt.m_cost);
        }
        puts("VL_DO_DANGLING(std::free(const_cast<char*>(vlSelf->vlNamep)), "
             "vlSelf->vlNamep);\n");
        puts("}\n");

        // C++ destructor
        puts("\n" + modName + "::~" + modName + "() {\n");
        emitSystemCSection(modp, VSystemCSectionType::DTOR);
        puts(modName + "__dtor(this);\n");
        puts("}\n");
    }

    void emitConfigureImp(const AstNodeModule* modp) {
        const string modName = EmitCUtil::prefixNameProtect(modp);

        if (v3Global.opt.coverage()) {
            openCommonImpFile();
            puts("\n");
            m_lazyDecls.emit("void " + modName + "__", protect("_configure_coverage"),
                             "(" + modName + "* vlSelf, bool first);");
        }

        if (v3Global.opt.coverage()) {
            puts("\nvoid " + modName + "::" + protect("__Vconfigure") + "(bool first) {\n");
            puts("(void)first;  // Prevent unused variable warning\n");
            puts(modName + "__" + protect("_configure_coverage") + "(this, first);\n");
            puts("}\n");
        }
    }
    void emitCoverageImp() {
        // Rather than putting out VL_COVER_INSERT calls directly, we do it via this
        // function. This gets around gcc slowness constructing all of the template
        // arguments.
        if (v3Global.opt.coverage()) {
            openCommonImpFile();
            puts("\n// Coverage\n");
            puts("void " + EmitCUtil::prefixNameProtect(m_modp) + "::__vlCoverInsert(");
            puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, bool localCounter, const char* filenamep, int lineno, "
                 "int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp, const char* "
                 "linescovp,\n");
            puts("const char* fsmVarp, const char* fsmFromp, const char* fsmTop, const char* "
                 "fsmTagp) {\n");
            if (v3Global.opt.threads() > 1) {
                puts("assert(sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));\n");
                puts("uint32_t* count32p = reinterpret_cast<uint32_t*>(countp);\n");
            } else {
                puts("uint32_t* count32p = countp;\n");
            }
            // static doesn't need save-restore as is constant
            puts("static uint32_t fake_zero_count = 0;\n");
            puts("std::string fullhier = std::string{vlNamep} + hierp;\n");
            puts("if (!fullhier.empty() && fullhier[0] == '.') fullhier = fullhier.substr(1);\n");
            // Global-counter users still redirect later duplicate instances
            // to fake_zero_count for default collapsed coverage. Object-local
            // counters must keep the real pointer so forcePerInstance can
            // report each hierarchy independently.
            puts("if (!enable && !localCounter) count32p = &fake_zero_count;\n");
            puts("*count32p = 0;\n");
            puts("VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), vlNamep, count32p,");
            puts("  \"filename\",filenamep,");
            puts("  \"lineno\",lineno,");
            puts("  \"column\",column,\n");
            puts("\"hier\",fullhier.c_str(),");
            puts("  \"page\",pagep,");
            puts("  \"comment\",commentp,");
            puts("  (linescovp[0] ? \"linescov\" : \"\"), linescovp,");
            puts("  (fsmVarp[0] ? \"fsm_var\" : \"\"), fsmVarp,");
            puts("  (fsmFromp[0] ? \"fsm_from\" : \"\"), fsmFromp,");
            puts("  (fsmTop[0] ? \"fsm_to\" : \"\"), fsmTop,");
            puts("  (fsmTagp[0] ? \"fsm_tag\" : \"\"), fsmTagp);\n");
            puts("}\n");
        }
        if (v3Global.opt.coverageToggle()) {
            openCommonImpFile();
            puts("\n// Toggle Coverage\n");
            puts("void " + EmitCUtil::prefixNameProtect(m_modp) + "::__vlCoverToggleInsert(");
            puts("int begin, int end, bool ranged, ");
            puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, bool localCounter, const char* filenamep, int lineno, "
                 "int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp) {\n");
            if (v3Global.opt.threads() > 1) {
                puts("assert(sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));\n");
            }
            puts("int step = (end >= begin) ? 1 : -1;\n");
            // range is inclusive
            puts("for (int i = begin; i != end + step; i += step) {\n");
            puts("for (int j = 0; j < 2; j++) {\n");
            if (v3Global.opt.threads() > 1) {
                puts("uint32_t* count32p = reinterpret_cast<uint32_t*>(countp);\n");
            } else {
                puts("uint32_t* count32p = countp;\n");
            }
            // static doesn't need save-restore as is constant
            puts("static uint32_t fake_zero_count = 0;\n");
            puts("std::string fullhier = std::string{vlNamep} + hierp;\n");
            puts("if (!fullhier.empty() && fullhier[0] == '.') fullhier = fullhier.substr(1);\n");
            puts("std::string commentWithIndex = commentp;\n");
            puts("if (ranged) commentWithIndex += '[' + std::to_string(i) + ']';\n");
            puts("commentWithIndex += j ? \":0->1\" : \":1->0\";\n");
            // Global-counter users still redirect later duplicate instances
            // to fake_zero_count for default collapsed coverage. Object-local
            // counters must keep the real pointer so forcePerInstance can
            // report each hierarchy independently.
            puts("if (!enable && !localCounter) count32p = &fake_zero_count;\n");
            puts("*count32p = 0;\n");
            puts("VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), vlNamep, count32p,");
            puts("  \"filename\",filenamep,");
            puts("  \"lineno\",lineno,");
            puts("  \"column\",column,\n");
            puts("\"hier\",fullhier.c_str(),");
            puts("  \"page\",pagep,");
            puts("  \"comment\",commentWithIndex.c_str(),");
            puts("  \"\", \"\");\n");  //  linescov argument, but in toggle coverage it is always
                                       //  empty
            puts("++countp;\n");
            puts("}\n");
            puts("}\n");
            puts("}\n");
        }
    }
    void emitSavableImp(const AstNodeModule* modp) {
        if (v3Global.opt.savable()) {
            openCommonImpFile();
            puts("\n// Savable\n");
            for (int de = 0; de < 2; ++de) {
                const string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
                const string funcname = de ? "__Vdeserialize" : "__Vserialize";
                const string op = de ? ">>" : "<<";
                // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
                putns(modp, "void " + EmitCUtil::prefixNameProtect(modp) + "::" + protect(funcname)
                                + "(" + classname + "& os) {\n");
                // Place a computed checksum to ensure proper structure save/restore formatting
                // OK if this hash includes some things we won't dump, since
                // just looking for loading the wrong model
                VHashSha512 hash;
                for (AstNode* const nodep : modp->stmtspList()) {
                    if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                        hash.insert(varp->name());
                        hash.insert(varp->dtypep()->width());
                    }
                }
                ofp()->printf("uint64_t __Vcheckval = 0x%" PRIx64 "ULL;\n",
                              static_cast<uint64_t>(hash.digestUInt64()));
                if (de) {
                    puts("os.readAssert(__Vcheckval);\n");
                } else {
                    puts("os << __Vcheckval;\n");
                }

                // Save context
                // If multiple models save the same context we'll save it multiple
                // times, but is harmless, and doing it otherwise would break
                // backwards compatibility.
                puts("os " + op + " vlSymsp->_vm_contextp__;\n");

                // Save all members
                for (AstNode* const nodep : modp->stmtspList()) {
                    if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                        if (varp->isIO() && modp->isTop() && optSystemC()) {
                            // System C top I/O doesn't need loading, as the
                            // lower level subinst code does it.
                        } else if (varp->isParam()) {
                        } else if (VN_IS(varp->dtypep(), ClosurePoolDType)) {
                            // Closure pools are not saved, they are simply memory pools
                        } else if (varp->basicp() && varp->basicp()->isNbaGenericQueue()) {
                            // NBAs enqueued in an eval are committed by its end. Those made by
                            // a DPI export called between evals are pending, so a save drops them
                        } else {
                            int vects = 0;
                            AstNodeDType* elementp = varp->dtypeSkipRefp();
                            for (AstUnpackArrayDType* arrayp = VN_CAST(elementp, UnpackArrayDType);
                                 arrayp; arrayp = VN_CAST(elementp, UnpackArrayDType)) {
                                const int vecnum = vects++;
                                UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                            "Should have swapped msb & lsb earlier.");
                                const string ivar = "__Vi"s + cvtToStr(vecnum);
                                puts("for (int __Vi" + cvtToStr(vecnum) + " = " + cvtToStr(0));
                                puts("; " + ivar + " < " + cvtToStr(arrayp->elementsConst()));
                                puts("; ++" + ivar + ") {\n");
                                elementp = arrayp->subDTypep()->skipRefp();
                            }
                            const AstBasicDType* const basicp = elementp->basicp();
                            // Want to detect types that are represented as arrays
                            // (i.e. packed types of more than 64 bits).
                            if (elementp->isWide()
                                && !(basicp && basicp->keyword() == VBasicDTypeKwd::STRING)) {
                                const int vecnum = vects++;
                                const string ivar = "__Vi"s + cvtToStr(vecnum);
                                puts("for (int __Vi" + cvtToStr(vecnum) + " = " + cvtToStr(0));
                                puts("; " + ivar + " < " + cvtToStr(elementp->widthWords()));
                                puts("; ++" + ivar + ") {\n");
                            }
                            putns(varp, "os" + op + varName(varp));
                            for (int v = 0; v < vects; ++v) puts("[__Vi" + cvtToStr(v) + "]");
                            puts(";\n");
                            for (int v = 0; v < vects; ++v) puts("}\n");
                        }
                    }
                }

                puts("}\n");
            }
        }
    }
    void emitCommonImpSlow() {
        // Create ctor/dtor statements. If these need splitting, they will be emitted
        // during construction so do this before opening the output file.
        for (AstNodeModule* const modp : m_modps) {
            if (!VN_IS(modp, Class)) createCtorDtorStmts(modp);
        }

        for (const AstNodeModule* const modp : m_modps) {
            VL_RESTORER(m_modp);
            m_modp = modp;
            if (!VN_IS(modp, Class)) {
                emitParamDefns(modp);
                emitCtorDtorImp(modp);
                emitConfigureImp(modp);
                emitCoverageImp();
            }
            emitSavableImp(modp);
        }

        if (ofp()) closeOutputFile();
    }
    void emitCommonImpFast() {
        for (const AstNodeModule* const modp : m_modps) {
            // Avoid creating empty output files, only needed for `systemc_implementation
            if (!scSection(modp, VSystemCSectionType::IMP).second) continue;
            openCommonImpFile();
            emitSystemCSection(modp, VSystemCSectionType::IMP);
        }

        if (ofp()) closeOutputFile();
    }
    void emitCFuncImp() {
        for (const AstNodeModule* const modp : m_modps) {
            VL_RESTORER(m_modp);
            VL_RESTORER(m_classOrPackagep);
            m_modp = modp;
            const AstClass* const classp = VN_CAST(modp, Class);
            m_classOrPackagep = classp ? classp->classOrPackagep() : VN_CAST(modp, ClassPackage);
            for (AstNode* const nodep : modp->stmtspList()) {
                AstCFunc* const funcp = VN_CAST(nodep, CFunc);
                if (!funcp || !isImpFunc(funcp)) continue;
                if (funcp->slow() != m_slow) continue;
                // Open output file only when needed, so not to create empty files
                if (!ofp()) openNextOutputFile(m_uniqueNames.get(m_fileBaseName));
                iterateConst(funcp);
            }
        }
        if (ofp()) closeOutputFile();
    }
    void splitOutputFile() {
        // Splitting file, so using parallel build.
        v3Global.useParallelBuild(true);
        closeOutputFile();
        openNextOutputFile(m_uniqueNames.get(m_fileBaseName));
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        if (splitNeeded()) splitOutputFile();
        EmitCFunc::visit(nodep);
    }

    EmitCImp(const std::vector<AstNodeModule*>& modps, const std::string& fileBaseName, bool slow)
        : m_modps{modps}
        , m_slow{slow}
        , m_fileBaseName{fileBaseName} {
        UINFO(5, "  Emitting implementation of " << fileBaseName);

        // Emit implementations of common parts
        if (m_slow) {
            emitCommonImpSlow();
        } else {
            emitCommonImpFast();
        }

        // Emit implementations of all AstCFunc
        emitCFuncImp();
    }
    ~EmitCImp() override = default;

public:
    // Whether the function is emitted by this visitor
    static bool isImpFunc(const AstCFunc* funcp) {
        return !funcp->dpiImportPrototype() && !funcp->dpiExportDispatcher();
    }

    static std::vector<AstCFile*> main(const std::vector<AstNodeModule*>& modps,
                                       const std::string& fileBaseName, bool slow) VL_MT_STABLE {
        EmitCImp emitCImp{modps, fileBaseName, slow};
        return emitCImp.getAndClearCfileps();
    }
};

//######################################################################
// Existing AstCFile emitter

class EmitCFile final : public EmitCFunc {
    explicit EmitCFile(AstCFile* cfilep) {
        openOutputFile(cfilep, "Generated C++");
        iterateConst(cfilep->tblockp());
        closeOutputFile();
    }
    ~EmitCFile() override = default;

public:
    static void main(AstCFile* cfilep) VL_MT_STABLE {
        if (!cfilep->tblockp()) return;
        EmitCFile{cfilep};
    }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcImp() {
    UINFO(2, __FUNCTION__ << ":");
    std::list<std::vector<AstCFile*>> cfiles;
    {
        // Make parent module pointers available.
        const EmitCParentModule emitCParentModule;
        // Used by EmitCImp
        const VNUser1InUse user1InUse;

        // Groups of modules emitted into the same files, with the base name of the files
        std::vector<std::pair<std::vector<AstNodeModule*>, std::string>> groups;

        // Process each module in turn, gathering classes to be emitted below
        std::vector<AstClassPackage*> clspkgps;  // Class packages, emitted with their class
        for (AstNode* const nodep : v3Global.rootp()->modulespList()) {
            AstNodeModule* const modp = VN_AS(nodep, NodeModule);
            if (modp->isConstPool()) continue;  // Emitted by V3EmitCConstPool
            if (VN_IS(modp, Class)) continue;  // Emitted with its package
            if (AstClassPackage* const clspkgp = VN_CAST(modp, ClassPackage)) {
                clspkgps.push_back(clspkgp);
                continue;
            }
            groups.emplace_back(std::vector<AstNodeModule*>{modp},
                                EmitCUtil::prefixNameProtect(modp));
        }

        // Cut the classes, in netlist order, into chunks of about one --output-split worth of
        // slow or fast code, each emitted into its own files, in parallel. Netlist order keeps
        // classes that use each other close, so the templates instantiated for a class (e.g.
        // VlClassRef) are compiled in fewer files. A class goes right after its package, so the
        // compiler sees them together.
        const size_t splitLimit = v3Global.opt.outputSplit();
        std::vector<std::vector<AstNodeModule*>> chunks;
        // Size of the slow and fast code of the current chunk, as measured for --output-split
        size_t slowCost = 0;
        size_t fastCost = 0;
        for (AstClassPackage* const clspkgp : clspkgps) {
            if (chunks.empty() || (splitLimit && std::max(slowCost, fastCost) >= splitLimit)) {
                chunks.emplace_back();
                slowCost = 0;
                fastCost = 0;
            }
            AstNodeModule* const pkgp = clspkgp;
            AstNodeModule* const clsp = clspkgp->classp();
            chunks.back().push_back(pkgp);
            chunks.back().push_back(clsp);
            for (const AstNodeModule* const implp : {pkgp, clsp}) {
                for (const AstNode* const stmtp : implp->stmtspList()) {
                    const AstCFunc* const funcp = VN_CAST(stmtp, CFunc);
                    if (!funcp || !EmitCImp::isImpFunc(funcp)) continue;
                    (funcp->slow() ? slowCost : fastCost) += funcp->nodeCount();
                }
            }
        }
        // Class code is split into multiple files, so use parallel build
        if (chunks.size() > 1) v3Global.useParallelBuild(true);

        // Emit all classes in the same chunk into the same files
        for (size_t i = 0; i < chunks.size(); ++i) {
            const std::string suffix = "_Classes_" + std::to_string(i);
            groups.emplace_back(std::move(chunks[i]),
                                EmitCUtil::topClassName() + "_" + VIdProtect::protect(suffix));
        }

        V3ThreadScope threadScope;

        // Emit each group
        for (const auto& group : groups) {
            for (const bool slow : {true, false}) {
                cfiles.emplace_back();
                std::vector<AstCFile*>& cfileps = cfiles.back();
                threadScope.enqueue([&group, slow, &cfileps] {
                    cfileps = EmitCImp::main(group.first, group.second, slow);
                });
            }
        }
    }
    // Add files to netlist
    for (const std::vector<AstCFile*>& cfileps : cfiles) {
        for (AstCFile* const cfilep : cfileps) v3Global.rootp()->addFilesp(cfilep);
    }
}

void V3EmitC::emitcFiles() {
    UINFO(2, __FUNCTION__ << ":");
    for (AstNodeFile* const filep : v3Global.rootp()->filespList()) {
        if (AstCFile* const cfilep = VN_CAST(filep, CFile)) EmitCFile::main(cfilep);
    }
}
