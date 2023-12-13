// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCFunc.h"
#include "V3ThreadPool.h"
#include "V3UniqueNames.h"

#include <map>
#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Visitor that gathers the headers required by an AstCFunc

class EmitCGatherDependencies final : VNVisitorConst {
    // Ordered set, as it is used as a key in another map.
    std::set<string> m_dependencies;  // Header names to be included in output C++ file

    // METHODS
    void addSymsDependency() { m_dependencies.insert(EmitCBase::symClassName()); }
    void addModDependency(const AstNodeModule* modp) {
        if (const AstClass* const classp = VN_CAST(modp, Class)) {
            m_dependencies.insert(EmitCBase::prefixNameProtect(classp->classOrPackagep()));
        } else {
            m_dependencies.insert(EmitCBase::prefixNameProtect(modp));
        }
    }
    void addDTypeDependency(const AstNodeDType* nodep) {
        if (const AstClassRefDType* const dtypep = VN_CAST(nodep, ClassRefDType)) {
            m_dependencies.insert(
                EmitCBase::prefixNameProtect(dtypep->classp()->classOrPackagep()));
        } else if (const AstNodeUOrStructDType* const dtypep
                   = VN_CAST(nodep, NodeUOrStructDType)) {
            if (!dtypep->packed()) {
                UASSERT_OBJ(dtypep->classOrPackagep(), nodep, "Unlinked struct package");
                m_dependencies.insert(EmitCBase::prefixNameProtect(dtypep->classOrPackagep()));
            }
        }
    }
    void addSelfDependency(VSelfPointerText selfPointer, AstNode* nodep) {
        if (selfPointer.isEmpty()) {
            // No self pointer (e.g.: function locals, const pool values, loose static methods),
            // so no dependency
        } else if (selfPointer.hasThis()) {
            // Dereferencing 'this', we need the definition of this module, which is also the
            // module that contains the variable.
            addModDependency(EmitCParentModule::get(nodep));
        } else {
            // Must be an absolute reference
            UASSERT_OBJ(selfPointer.isVlSym(), nodep,
                        "Unknown self pointer: '" << selfPointer.asString() << "'");
            // Dereferencing vlSymsp, so we need it's definition...
            addSymsDependency();
        }
    }

    // VISITORS
    void visit(AstCCall* nodep) override {
        addSelfDependency(nodep->selfPointer(), nodep->funcp());
        iterateChildrenConst(nodep);
    }
    void visit(AstCNew* nodep) override {
        addSymsDependency();
        addDTypeDependency(nodep->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstCMethodCall* nodep) override {
        addDTypeDependency(nodep->fromp()->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstNewCopy* nodep) override {
        addSymsDependency();
        addDTypeDependency(nodep->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstMemberSel* nodep) override {
        addDTypeDependency(nodep->fromp()->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstStructSel* nodep) override {
        addDTypeDependency(nodep->fromp()->dtypep());
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        addSelfDependency(nodep->selfPointer(), nodep->varp());
        iterateChildrenConst(nodep);
    }
    void visit(AstCoverDecl* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstCoverInc* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstDumpCtl* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstScopeName* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstPrintTimeScale* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstTimeFormat* nodep) override {
        addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeSimpleText* nodep) override {
        if (nodep->text().find("vlSymsp") != string::npos) addSymsDependency();
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTOR
    explicit EmitCGatherDependencies(AstCFunc* cfuncp) {
        // Strictly speaking, for loose methods, we could get away with just a forward
        // declaration of the receiver class, but their body very likely includes at least one
        // relative reference, so we are probably not loosing much.
        addModDependency(EmitCParentModule::get(cfuncp));
        iterateConst(cfuncp);
    }

public:
    static const std::set<std::string> gather(AstCFunc* cfuncp) {
        const EmitCGatherDependencies visitor{cfuncp};
        return std::move(visitor.m_dependencies);
    }
};

//######################################################################
// Internal EmitC implementation

class EmitCImp final : EmitCFunc {
    // MEMBERS
    const AstNodeModule* const m_fileModp;  // Files names/headers constructed using this module
    const bool m_slow;  // Creating __Slow file
    const std::set<string>* m_requiredHeadersp;  // Header files required by output file
    std::string m_subFileName;  // substring added to output filenames
    V3UniqueNames m_uniqueNames;  // For generating unique file names
    std::deque<AstCFile*>& m_cfilesr;  // cfiles generated by this emit

    // METHODS
    void openNextOutputFile(const std::set<string>& headers, const string& subFileName) {
        UASSERT(!m_ofp, "Output file already open");

        splitSizeReset();  // Reset file size tracking
        m_lazyDecls.reset();  // Need to emit new lazy declarations

        if (v3Global.opt.lintOnly()) {
            // Unfortunately we have some lint checks here, so we can't just skip processing.
            // We should move them to a different stage.
            const string filename = VL_DEV_NULL;
            m_cfilesr.push_back(createCFile(filename, /* slow: */ m_slow, /* source: */ true));
            m_ofp = new V3OutCFile{filename};
        } else {
            string filename = v3Global.opt.makeDir() + "/" + prefixNameProtect(m_fileModp);
            if (!subFileName.empty()) {
                filename += "__" + subFileName;
                filename = m_uniqueNames.get(filename);
            }
            if (m_slow) filename += "__Slow";
            filename += ".cpp";
            m_cfilesr.push_back(createCFile(filename, /* slow: */ m_slow, /* source: */ true));
            m_ofp = v3Global.opt.systemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};
        }

        putsHeader();
        puts("// DESCRIPTION: Verilator output: Design implementation internals\n");
        puts("// See " + topClassName() + ".h for the primary calling header\n");

        puts("\n");
        puts("#include \"" + pchClassName() + ".h\"\n");
        for (const string& name : headers) puts("#include \"" + name + ".h\"\n");

        emitTextSection(m_modp, VNType::atScImpHdr);
    }

    void emitStaticVarDefns(const AstNodeModule* modp) {
        // Emit static variable definitions
        const string modName = prefixNameProtect(modp);
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isStatic()) {
                    puts(varp->vlArgType(true, false, false, modName));
                    puts(";\n");
                }
            }
        }
    }
    void emitParamDefns(const AstNodeModule* modp) {
        const string modName = prefixNameProtect(modp);
        bool first = true;
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isParam()) {
                    if (first) {
                        puts("\n");
                        putsDecoration("// Parameter definitions for " + modName + "\n");
                        first = false;
                    }
                    UASSERT_OBJ(varp->valuep(), nodep, "No init for a param?");
                    // Only C++ LiteralTypes can be constexpr
                    const bool canBeConstexpr = varp->dtypep()->isLiteralType();
                    puts(canBeConstexpr ? "constexpr " : "const ");
                    const string scopedName = modName + "::" + varp->nameProtect();
                    puts(varp->dtypep()->cType(scopedName, false, false));
                    if (!canBeConstexpr) {
                        puts(" = ");
                        emitConstInit(varp->valuep());
                    }
                    puts(";\n");
                }
            }
        }
        if (!first) puts("\n");
    }
    void emitCtorImp(const AstNodeModule* modp) {
        const string modName = prefixNameProtect(modp);

        puts("\n");
        m_lazyDecls.emit("void " + modName + "__", protect("_ctor_var_reset"),
                         "(" + modName + "* vlSelf);");
        puts("\n");

        puts(modName + "::" + modName + "(" + symClassName() + "* symsp, const char* v__name)\n");
        puts("    : VerilatedModule{v__name}\n");

        ofp()->indentInc();
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (const AstBasicDType* const dtypep
                    = VN_CAST(varp->dtypeSkipRefp(), BasicDType)) {
                    if (dtypep->keyword().isMTaskState()) {
                        puts(", ");
                        puts(varp->nameProtect());
                        puts("(");
                        iterateConst(varp->valuep());
                        puts(")\n");
                    } else if (varp->isIO() && varp->isSc()) {
                        puts(", ");
                        puts(varp->nameProtect());
                        puts("(");
                        putsQuoted(varp->nameProtect());
                        puts(")\n");
                    } else if (dtypep->isDelayScheduler()) {
                        puts(", ");
                        puts(varp->nameProtect());
                        puts("{*symsp->_vm_contextp__}\n");
                    }
                }
            }
        }
        puts(", vlSymsp{symsp}\n");
        ofp()->indentDec();

        puts(" {\n");

        putsDecoration("// Reset structure values\n");
        puts(modName + "__" + protect("_ctor_var_reset") + "(this);\n");
        emitTextSection(modp, VNType::atScCtor);

        puts("}\n");
    }
    void emitConfigureImp(const AstNodeModule* modp) {
        const string modName = prefixNameProtect(modp);

        if (v3Global.opt.coverage()) {
            puts("\n");
            m_lazyDecls.emit("void " + modName + "__", protect("_configure_coverage"),
                             "(" + modName + "* vlSelf, bool first);");
        }

        puts("\nvoid " + modName + "::" + protect("__Vconfigure") + "(bool first) {\n");
        puts("if (false && first) {}  // Prevent unused\n");
        if (v3Global.opt.coverage()) {
            puts(modName + "__" + protect("_configure_coverage") + "(this, first);\n");
        }
        puts("}\n");
        splitSizeInc(10);
    }
    void emitCoverageImp() {
        if (v3Global.opt.coverage()) {
            puts("\n// Coverage\n");
            // Rather than putting out VL_COVER_INSERT calls directly, we do it via this
            // function. This gets around gcc slowness constructing all of the template
            // arguments.
            puts("void " + prefixNameProtect(m_modp) + "::__vlCoverInsert(");
            puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp, const char* "
                 "linescovp) "
                 "{\n");
            if (v3Global.opt.threads() > 1) {
                puts("assert(sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));\n");
                puts("uint32_t* count32p = reinterpret_cast<uint32_t*>(countp);\n");
            } else {
                puts("uint32_t* count32p = countp;\n");
            }
            // static doesn't need save-restore as is constant
            puts("static uint32_t fake_zero_count = 0;\n");
            // Used for second++ instantiation of identical bin
            puts("if (!enable) count32p = &fake_zero_count;\n");
            puts("*count32p = 0;\n");
            puts("VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), count32p,");
            puts("  \"filename\",filenamep,");
            puts("  \"lineno\",lineno,");
            puts("  \"column\",column,\n");
            // Need to move hier into scopes and back out if do this
            // puts( "\"hier\",std::string{vlSymsp->name()} + hierp,");
            puts("\"hier\",std::string{name()} + hierp,");
            puts("  \"page\",pagep,");
            puts("  \"comment\",commentp,");
            puts("  (linescovp[0] ? \"linescov\" : \"\"), linescovp);\n");
            puts("}\n");
            splitSizeInc(10);
        }
    }
    void emitDestructorImp(const AstNodeModule* modp) {
        puts("\n");
        puts(prefixNameProtect(modp) + "::~" + prefixNameProtect(modp) + "() {\n");
        emitTextSection(modp, VNType::atScDtor);
        puts("}\n");
        splitSizeInc(10);
    }
    void emitSavableImp(const AstNodeModule* modp) {
        if (v3Global.opt.savable()) {
            puts("\n// Savable\n");
            for (int de = 0; de < 2; ++de) {
                const string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
                const string funcname = de ? "__Vdeserialize" : "__Vserialize";
                const string op = de ? ">>" : "<<";
                // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
                puts("void " + prefixNameProtect(modp) + "::" + protect(funcname) + "(" + classname
                     + "& os) {\n");
                // Place a computed checksum to ensure proper structure save/restore formatting
                // OK if this hash includes some things we won't dump, since
                // just looking for loading the wrong model
                VHashSha256 hash;
                for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
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
                for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                    if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                        if (varp->isIO() && modp->isTop() && optSystemC()) {
                            // System C top I/O doesn't need loading, as the
                            // lower level subinst code does it.
                        } else if (varp->isParam()) {
                        } else if (varp->isStatic() && varp->isConst()) {
                        } else if (varp->basicp() && varp->basicp()->isTriggerVec()) {
                        } else {
                            int vects = 0;
                            AstNodeDType* elementp = varp->dtypeSkipRefp();
                            for (AstUnpackArrayDType* arrayp = VN_CAST(elementp, UnpackArrayDType);
                                 arrayp; arrayp = VN_CAST(elementp, UnpackArrayDType)) {
                                const int vecnum = vects++;
                                UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                            "Should have swapped msb & lsb earlier.");
                                const string ivar = string{"__Vi"} + cvtToStr(vecnum);
                                puts("for (int __Vi" + cvtToStr(vecnum) + " = " + cvtToStr(0));
                                puts("; " + ivar + " < " + cvtToStr(arrayp->elementsConst()));
                                puts("; ++" + ivar + ") {\n");
                                elementp = arrayp->subDTypep()->skipRefp();
                            }
                            const AstBasicDType* const basicp = elementp->basicp();
                            // Do not save MTask state, only matters within an evaluation
                            if (basicp && basicp->keyword().isMTaskState()) continue;
                            // Want to detect types that are represented as arrays
                            // (i.e. packed types of more than 64 bits).
                            if (elementp->isWide()
                                && !(basicp && basicp->keyword() == VBasicDTypeKwd::STRING)) {
                                const int vecnum = vects++;
                                const string ivar = string{"__Vi"} + cvtToStr(vecnum);
                                puts("for (int __Vi" + cvtToStr(vecnum) + " = " + cvtToStr(0));
                                puts("; " + ivar + " < " + cvtToStr(elementp->widthWords()));
                                puts("; ++" + ivar + ") {\n");
                            }
                            puts("os" + op + varp->nameProtect());
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
    // Predicate to check if we actually need to emit anything into the common implementation file.
    // Used to avoid creating empty output files.
    bool hasCommonImp(const AstNodeModule* modp) const {
        // Nothing to emit if no module!
        if (!modp) return false;
        // We always need the slow file
        if (m_slow) return true;
        // The fast file is only required when we have ScImp nodes
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, ScImp)) return true;
        }
        return false;
    }
    // Actually emit common implementation contents for given AstNodeModule
    void doCommonImp(const AstNodeModule* modp) {
        if (m_slow) {
            emitStaticVarDefns(modp);
            if (!VN_IS(modp, Class)) {
                emitParamDefns(modp);
                emitCtorImp(modp);
                emitConfigureImp(modp);
                emitDestructorImp(modp);
                emitCoverageImp();
            }
            emitSavableImp(modp);
        } else {
            // From `systemc_implementation
            emitTextSection(modp, VNType::atScImp);
        }
    }
    void emitCommonImp(const AstNodeModule* modp) {
        const AstClass* const classp
            = VN_IS(modp, ClassPackage) ? VN_AS(modp, ClassPackage)->classp() : nullptr;

        if (hasCommonImp(modp) || hasCommonImp(classp)) {
            std::set<string> headers;
            headers.insert(prefixNameProtect(m_fileModp));
            headers.insert(symClassName());

            openNextOutputFile(headers, "");

            doCommonImp(modp);
            if (classp) {
                VL_RESTORER(m_modp);
                m_modp = classp;
                doCommonImp(classp);
            }

            VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
        }
    }
    void emitCFuncImp(const AstNodeModule* modp) {
        // Partition functions based on which module definitions they require, by building a
        // map from "AstNodeModules whose definitions are required" -> "functions that need
        // them"
        std::map<const std::set<string>, std::vector<AstCFunc*>> depSet2funcps;

        const auto gather = [this, &depSet2funcps](const AstNodeModule* modp) {
            for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (AstCFunc* const funcp = VN_CAST(nodep, CFunc)) {
                    // TRACE_* and DPI handled elsewhere
                    if (funcp->isTrace()) continue;
                    if (funcp->dpiImportPrototype()) continue;
                    if (funcp->dpiExportDispatcher()) continue;
                    if (funcp->slow() != m_slow) continue;
                    const auto& depSet = EmitCGatherDependencies::gather(funcp);
                    depSet2funcps[depSet].push_back(funcp);
                }
            }
        };

        gather(modp);
        if (const AstClassPackage* const packagep = VN_CAST(modp, ClassPackage)) {
            gather(packagep->classp());
        }

        // Emit all functions in each dependency set into separate files
        for (const auto& pair : depSet2funcps) {
            m_requiredHeadersp = &pair.first;
            // Compute the hash of the dependencies, so we can add it to the filenames to
            // disambiguate them
            V3Hash hash;
            for (const string& name : *m_requiredHeadersp) hash += name;
            m_subFileName = "DepSet_" + hash.toString();
            // Open output file
            openNextOutputFile(*m_requiredHeadersp, m_subFileName);
            // Emit functions in this dependency set
            for (AstCFunc* const funcp : pair.second) {
                VL_RESTORER(m_modp);
                m_modp = EmitCParentModule::get(funcp);
                iterateConst(funcp);
            }
            // Close output file
            VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
        }
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        if (splitNeeded()) {
            // Splitting file, so using parallel build.
            v3Global.useParallelBuild(true);
            // Close old file
            VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
            // Open a new file
            openNextOutputFile(*m_requiredHeadersp, m_subFileName);
        }

        EmitCFunc::visit(nodep);
    }

    explicit EmitCImp(const AstNodeModule* modp, bool slow, std::deque<AstCFile*>& cfilesr)
        : m_fileModp{modp}
        , m_slow{slow}
        , m_cfilesr{cfilesr} {
        UINFO(5, "  Emitting implementation of " << prefixNameProtect(modp) << endl);

        m_modp = modp;

        // Emit implementation of this module, if this is an AstClassPackage, then put the
        // corresponding AstClass implementation in the same file as often optimizations are
        // possible when both are seen by the compiler
        // TODO: is the above comment still true?

        // Emit implementations of common parts
        emitCommonImp(modp);

        // Emit implementations of all AstCFunc
        emitCFuncImp(modp);
    }
    ~EmitCImp() override = default;

public:
    static void main(const AstNodeModule* modp, bool slow, std::deque<AstCFile*>& cfilesr) {
        EmitCImp{modp, slow, cfilesr};
    }
};

//######################################################################
// Tracing routines

class EmitCTrace final : EmitCFunc {
    // NODE STATE/TYPES
    // None allowed to support threaded emitting

    // MEMBERS
    const bool m_slow;  // Making slow file
    int m_enumNum = 0;  // Enumeration number (whole netlist)
    V3UniqueNames m_uniqueNames;  // For generating unique file names
    std::unordered_map<AstNode*, int> m_enumNumMap;  // EnumDType to enumeration number
    std::deque<AstCFile*>& m_cfilesr;  // cfiles generated by this emit

    // METHODS
    void openNextOutputFile() {
        UASSERT(!m_ofp, "Output file already open");

        splitSizeReset();  // Reset file size tracking
        m_lazyDecls.reset();  // Need to emit new lazy declarations

        string filename
            = (v3Global.opt.makeDir() + "/" + topClassName() + "_" + protect("_Trace"));
        filename = m_uniqueNames.get(filename);
        if (m_slow) filename += "__Slow";
        filename += ".cpp";

        AstCFile* const cfilep = createCFile(filename, m_slow, true /*source*/);
        cfilep->support(true);
        m_cfilesr.push_back(cfilep);

        if (optSystemC()) {
            m_ofp = new V3OutScFile{filename};
        } else {
            m_ofp = new V3OutCFile{filename};
        }
        putsHeader();
        puts("// DESCR"
             "IPTION: Verilator output: Tracing implementation internals\n");

        // Includes
        puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
        puts("#include \"" + symClassName() + ".h\"\n");
        puts("\n");
    }

    bool emitTraceIsScBv(AstTraceInc* nodep) {
        const AstVarRef* const varrefp = VN_CAST(nodep->declp()->valuep(), VarRef);
        if (!varrefp) return false;
        AstVar* const varp = varrefp->varp();
        return varp->isSc() && varp->isScBv();
    }

    bool emitTraceIsScBigUint(AstTraceInc* nodep) {
        const AstVarRef* const varrefp = VN_CAST(nodep->declp()->valuep(), VarRef);
        if (!varrefp) return false;
        AstVar* const varp = varrefp->varp();
        return varp->isSc() && varp->isScBigUint();
    }

    bool emitTraceIsScUint(AstTraceInc* nodep) {
        const AstVarRef* const varrefp = VN_CAST(nodep->declp()->valuep(), VarRef);
        if (!varrefp) return false;
        AstVar* const varp = varrefp->varp();
        return varp->isSc() && varp->isScUint();
    }

    void emitTraceInitOne(AstTraceDecl* nodep, int enumNum) {
        if (nodep->dtypep()->basicp()->isDouble()) {
            puts("tracep->declDouble(");
        } else if (nodep->isWide()) {
            puts("tracep->declArray(");
        } else if (nodep->isQuad()) {
            puts("tracep->declQuad(");
        } else if (nodep->bitRange().ranged()) {
            puts("tracep->declBus(");
        } else if (nodep->dtypep()->basicp()->isEvent()) {
            puts("tracep->declEvent(");
        } else {
            puts("tracep->declBit(");
        }

        // Code
        puts("c+" + cvtToStr(nodep->code()));
        if (nodep->arrayRange().ranged()) puts("+i*" + cvtToStr(nodep->widthWords()));

        // Function index
        puts(",");
        puts(cvtToStr(nodep->fidx()));

        // Name
        puts(",");
        putsQuoted(VIdProtect::protectWordsIf(nodep->showname(), nodep->protect()));

        // Enum number
        puts("," + cvtToStr(enumNum));

        // Direction
        if (nodep->declDirection().isInoutish()) {
            puts(", VerilatedTraceSigDirection::INOUT");
        } else if (nodep->declDirection().isWritable()) {
            puts(", VerilatedTraceSigDirection::OUTPUT");
        } else if (nodep->declDirection().isNonOutput()) {
            puts(", VerilatedTraceSigDirection::INPUT");
        } else {
            puts(", VerilatedTraceSigDirection::NONE");
        }

        // Kind
        puts(", VerilatedTraceSigKind::");
        puts(nodep->varType().traceSigKind());

        // Type
        puts(", VerilatedTraceSigType::");
        puts(nodep->dtypep()->basicp()->keyword().traceSigType());

        // Array range
        if (nodep->arrayRange().ranged()) {
            puts(", true,(i+" + cvtToStr(nodep->arrayRange().lo()) + ")");
        } else {
            puts(", false,-1");
        }

        // Bit range
        if (!nodep->dtypep()->basicp()->isDouble() && nodep->bitRange().ranged()) {
            puts(", " + cvtToStr(nodep->bitRange().left()) + ","
                 + cvtToStr(nodep->bitRange().right()));
        }

        //
        puts(");");
    }

    int emitTraceDeclDType(AstNodeDType* nodep) {
        // Return enum number or -1 for none
        if (v3Global.opt.traceFormat().fst()) {
            // Skip over refs-to-refs, but stop before final ref so can get data type name
            // Alternatively back in V3Width we could push enum names from upper typedefs
            if (AstEnumDType* const enump = VN_CAST(nodep->skipRefToEnump(), EnumDType)) {
                int enumNum = m_enumNumMap[enump];
                if (!enumNum) {
                    enumNum = ++m_enumNum;
                    m_enumNumMap[enump] = enumNum;
                    int nvals = 0;
                    puts("{\n");
                    puts("const char* " + protect("__VenumItemNames") + "[]\n");
                    puts("= {");
                    for (AstEnumItem* itemp = enump->itemsp(); itemp;
                         itemp = VN_AS(itemp->nextp(), EnumItem)) {
                        if (++nvals > 1) puts(", ");
                        putbs("\"" + itemp->prettyName() + "\"");
                    }
                    puts("};\n");
                    nvals = 0;
                    puts("const char* " + protect("__VenumItemValues") + "[]\n");
                    puts("= {");
                    for (AstEnumItem* itemp = enump->itemsp(); itemp;
                         itemp = VN_AS(itemp->nextp(), EnumItem)) {
                        AstConst* const constp = VN_AS(itemp->valuep(), Const);
                        if (++nvals > 1) puts(", ");
                        putbs("\"" + constp->num().displayed(nodep, "%0b") + "\"");
                    }
                    puts("};\n");
                    puts("tracep->declDTypeEnum(" + cvtToStr(enumNum) + ", \""
                         + enump->prettyName() + "\", " + cvtToStr(nvals) + ", "
                         + cvtToStr(enump->widthMin()) + ", " + protect("__VenumItemNames") + ", "
                         + protect("__VenumItemValues") + ");\n");
                    puts("}\n");
                }
                return enumNum;
            }
        }
        return -1;
    }

    void emitTraceChangeOne(AstTraceInc* nodep, int arrayindex) {
        iterateAndNextConstNull(nodep->precondsp());
        // Note: Both VTraceType::CHANGE and VTraceType::FULL use the 'full' methods
        const std::string func = nodep->traceType() == VTraceType::CHANGE ? "chg" : "full";
        bool emitWidth = true;
        if (nodep->dtypep()->basicp()->isDouble()) {
            puts("bufp->" + func + "Double");
            emitWidth = false;
        } else if (nodep->isWide() || emitTraceIsScBv(nodep) || emitTraceIsScBigUint(nodep)) {
            puts("bufp->" + func + "WData");
        } else if (nodep->isQuad()) {
            puts("bufp->" + func + "QData");
        } else if (nodep->declp()->widthMin() > 16) {
            puts("bufp->" + func + "IData");
        } else if (nodep->declp()->widthMin() > 8) {
            puts("bufp->" + func + "SData");
        } else if (nodep->declp()->widthMin() > 1) {
            puts("bufp->" + func + "CData");
        } else if (nodep->dtypep()->basicp()->isEvent()) {
            puts("bufp->" + func + "Event");
            emitWidth = false;
        } else {
            puts("bufp->" + func + "Bit");
            emitWidth = false;
        }

        const uint32_t offset = (arrayindex < 0) ? 0 : (arrayindex * nodep->declp()->widthWords());
        const uint32_t code = nodep->declp()->code() + offset;
        // Note: Both VTraceType::CHANGE and VTraceType::FULL use the 'full' methods
        puts(v3Global.opt.useTraceOffload() && nodep->traceType() == VTraceType::CHANGE
                 ? "(base+"
                 : "(oldp+");
        puts(cvtToStr(code - nodep->baseCode()));
        puts(",");
        emitTraceValue(nodep, arrayindex);
        if (emitWidth) puts("," + cvtToStr(nodep->declp()->widthMin()));
        puts(");\n");
    }

    void emitTraceValue(AstTraceInc* nodep, int arrayindex) {
        if (AstVarRef* const varrefp = VN_CAST(nodep->valuep(), VarRef)) {
            AstVar* const varp = varrefp->varp();
            if (varp->isEvent()) { puts("&"); }
            puts("(");
            if (emitTraceIsScBigUint(nodep)) {
                puts("(uint32_t*)");
            } else if (emitTraceIsScBv(nodep)) {
                puts("VL_SC_BV_DATAP(");
            }
            iterateConst(varrefp);  // Put var name out
            // Tracing only supports 1D arrays
            if (nodep->declp()->arrayRange().ranged()) {
                if (arrayindex == -2) {
                    puts("[i]");
                } else if (arrayindex == -1) {
                    puts("[0]");
                } else {
                    puts("[" + cvtToStr(arrayindex) + "]");
                }
            }
            if (varp->isSc()) puts(".read()");
            if (emitTraceIsScUint(nodep)) {
                puts(nodep->isQuad() ? ".to_uint64()" : ".to_uint()");
            } else if (emitTraceIsScBigUint(nodep)) {
                puts(".get_raw()");
            } else if (emitTraceIsScBv(nodep)) {
                puts(")");
            }
            puts(")");
        } else {
            puts("(");
            iterateConst(nodep->valuep());
            puts(")");
        }
    }

    // VISITORS
    using EmitCFunc::visit;  // Suppress hidden overloaded virtual function warning
    void visit(AstCFunc* nodep) override {
        if (!nodep->isTrace()) return;
        if (nodep->slow() != m_slow) return;

        if (splitNeeded()) {
            // Splitting file, so using parallel build.
            v3Global.useParallelBuild(true);
            // Close old file
            VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
            // Open a new file
            openNextOutputFile();
        }

        EmitCFunc::visit(nodep);
    }
    void visit(AstTracePushPrefix* nodep) override {
        puts("tracep->pushPrefix(");
        putsQuoted(VIdProtect::protectWordsIf(nodep->prefix(), nodep->protect()));
        puts(", VerilatedTracePrefixType::");
        puts(nodep->prefixType().ascii());
        puts(");\n");
    }
    void visit(AstTracePopPrefix* nodep) override {  //
        puts("tracep->popPrefix();\n");
    }
    void visit(AstTraceDecl* nodep) override {
        const int enumNum = emitTraceDeclDType(nodep->dtypep());
        if (nodep->arrayRange().ranged()) {
            puts("for (int i = 0; i < " + cvtToStr(nodep->arrayRange().elements()) + "; ++i) {\n");
            emitTraceInitOne(nodep, enumNum);
            puts("\n}\n");
        } else {
            emitTraceInitOne(nodep, enumNum);
            puts("\n");
        }
    }
    void visit(AstTraceInc* nodep) override {
        if (nodep->declp()->arrayRange().ranged()) {
            // It traces faster if we unroll the loop
            for (int i = 0; i < nodep->declp()->arrayRange().elements(); i++) {
                emitTraceChangeOne(nodep, i);
            }
        } else {
            emitTraceChangeOne(nodep, -1);
        }
    }

    explicit EmitCTrace(AstNodeModule* modp, bool slow, std::deque<AstCFile*>& cfilesr)
        : m_slow{slow}
        , m_cfilesr{cfilesr} {
        m_modp = modp;
        // Open output file
        openNextOutputFile();
        // Emit functions
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstCFunc* const funcp = VN_CAST(nodep, CFunc)) { iterateConst(funcp); }
        }
        // Close output file
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
    ~EmitCTrace() override = default;

public:
    static void main(AstNodeModule* modp, bool slow, std::deque<AstCFile*>& cfilesr) VL_MT_STABLE {
        EmitCTrace{modp, slow, cfilesr};
    }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcImp() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Make parent module pointers available.
    const EmitCParentModule emitCParentModule;
    std::list<std::deque<AstCFile*>> cfiles;
    std::list<std::future<void>> futures;

    // Process each module in turn
    for (const AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Class)) continue;  // Imped with ClassPackage
        const AstNodeModule* const modp = VN_AS(nodep, NodeModule);
        cfiles.emplace_back();
        auto& slowCfilesr = cfiles.back();
        futures.push_back(V3ThreadPool::s().enqueue(
            [modp, &slowCfilesr]() { EmitCImp::main(modp, /* slow: */ true, slowCfilesr); }));
        cfiles.emplace_back();
        auto& fastCfilesr = cfiles.back();
        futures.push_back(V3ThreadPool::s().enqueue(
            [modp, &fastCfilesr]() { EmitCImp::main(modp, /* slow: */ false, fastCfilesr); }));
    }

    // Emit trace routines (currently they can only exist in the top module)
    if (v3Global.opt.trace() && !v3Global.opt.lintOnly()) {
        cfiles.emplace_back();
        auto& slowCfilesr = cfiles.back();
        futures.push_back(V3ThreadPool::s().enqueue([&slowCfilesr]() {
            EmitCTrace::main(v3Global.rootp()->topModulep(), /* slow: */ true, slowCfilesr);
        }));
        cfiles.emplace_back();
        auto& fastCfilesr = cfiles.back();
        futures.push_back(V3ThreadPool::s().enqueue([&fastCfilesr]() {
            EmitCTrace::main(v3Global.rootp()->topModulep(), /* slow: */ false, fastCfilesr);
        }));
    }
    // Wait for futures
    V3ThreadPool::waitForFutures(futures);
    for (const auto& collr : cfiles) {
        for (const auto cfilep : collr) v3Global.rootp()->addFilesp(cfilep);
    }
}

void V3EmitC::emitcFiles() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    for (AstNodeFile* filep = v3Global.rootp()->filesp(); filep;
         filep = VN_AS(filep->nextp(), NodeFile)) {
        AstCFile* const cfilep = VN_CAST(filep, CFile);
        if (cfilep && cfilep->tblockp()) {
            V3OutCFile of{cfilep->name()};
            of.puts("// DESCR"
                    "IPTION: Verilator generated C++\n");
            const EmitCFunc visitor{cfilep->tblockp(), &of, true};
        }
    }
}
