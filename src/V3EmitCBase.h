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

#ifndef VERILATOR_V3EMITCBASE_H_
#define VERILATOR_V3EMITCBASE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3File.h"

#include <cmath>
#include <cstdarg>

//######################################################################
// Set user4p in all CFunc, Var, and coverage declarations to point to the
// containing AstNodeModule

class EmitCParentModule final {
    // NODE STATE
    //   AstCFunc::user4p()          AstNodeModule* Parent module pointer
    //   AstVar::user4p()            AstNodeModule* Parent module pointer
    //   AstNodeCoverDecl::user4p()  AstNodeModule* Parent module pointer
    const VNUser4InUse user4InUse;

public:
    EmitCParentModule();
    VL_UNCOPYABLE(EmitCParentModule);

    static const AstNodeModule* get(const AstNode* nodep) VL_MT_STABLE {
        return VN_AS(nodep->user4p(), NodeModule);
    }
};

//######################################################################
// EmitC-related utility functions

class EmitCUtil final {
public:
    static string voidSelfAssign(const AstNodeModule* modp) {
        const string className = prefixNameProtect(modp);
        return className + "* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<" + className
               + "*>(voidSelf);\n";
    }
    static string pchClassName() VL_MT_STABLE { return v3Global.opt.prefix() + "__pch"; }
    static string symClassName() VL_MT_STABLE {
        return v3Global.opt.prefix() + "_" + VIdProtect::protect("_Syms");
    }
    static string symClassVar() { return symClassName() + "* __restrict vlSymsp"; }
    static string symClassAssign() {
        return symClassName() + "* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;\n";
    }
    static string topClassName() VL_MT_SAFE {  // Return name of top wrapper module
        return v3Global.opt.prefix();
    }
    // Split a pretty path below the model into the name it is below, as an index into the
    // run-time names (0 for the model, e.g. in a package, else AstNetlist::l2Names() index plus
    // one), and the rest of the path
    static std::pair<size_t, std::string> splitTopPath(const std::string& path) {
        const std::vector<std::string>& tops = v3Global.rootp()->l2Names();
        for (size_t i = 0; i < tops.size(); ++i) {
            if (path == tops[i]) return {i + 1, ""};
            if (VString::startsWith(path, tops[i] + ".")) {
                return {i + 1, path.substr(tops[i].size() + 1)};
            }
        }
        return {0, path};
    }
    static std::string topNamesVar(bool protect) {
        return protect && v3Global.opt.protectIds() ? "__Vm_topNamesProt" : "__Vm_topNames";
    }
    static std::string topNameExpr(size_t index, bool protect) {
        return "vlSymsp->" + topNamesVar(protect) + "[" + std::to_string(index) + "].c_str()";
    }
    // Expression for the run-time name of the given path below the model
    static std::string instNameExpr(const std::string& path, bool protect) {
        const std::pair<size_t, std::string> top = splitTopPath(path);
        const std::string topName = topNameExpr(top.first, protect);
        if (top.second.empty()) return topName;
        return "Verilated::catName(" + topName + ", \""
               + V3OutFormatter::quoteNameControls(VIdProtect::protectWordsIf(top.second, protect))
               + "\")";
    }
    // Return name of the VlExecGraph describing an AstExecGraph
    static string execGraphName(const AstExecGraph* nodep) {
        return topClassName() + "__ExecGraph__" + nodep->nameProtect();
    }
    // Name of a constant pool variable
    static std::string constPoolName(const AstVar* varp) {
        UASSERT_OBJ(varp->constPoolEntry(), varp, "Not a constant pool variable");
        return topClassName() + "__ConstPool__" + varp->nameProtect();
    }
    // Return C++ class name for a module/class object
    static string prefixNameProtect(const AstNode* nodep) VL_MT_STABLE;
};

//######################################################################
// Base Visitor class -- holds output file pointer

class EmitCBaseVisitorConst VL_NOT_FINAL : public VNVisitorConst {
public:
    // TYPES
    // Rendered text statements, each with its cost, for splitting them into sub-functions
    class TextStmts final {
    public:
        struct Stmt final {
            std::string m_text;  // Statement text
            size_t m_cost;  // Cost of statement, for splitting
        };

    private:
        std::vector<Stmt> m_stmts;  // Statements

    public:
        // Add a statement
        void add(const std::string& stmt) {
            const size_t cost = stmt.empty() || VString::startsWith(stmt, "//")
                                    ? 0  // Blanks and comments are free
                                    : AstNode::INSTR_COUNT_CTOR_DTOR;
            m_stmts.push_back({stmt, cost});
        }
        size_t size() const { return m_stmts.size(); }
        const Stmt& operator[](size_t i) const { return m_stmts[i]; }
        std::vector<Stmt>::const_iterator begin() const { return m_stmts.begin(); }
        std::vector<Stmt>::const_iterator end() const { return m_stmts.end(); }
    };

private:
    // STATE
    V3OutCFile* m_ofp = nullptr;  // File handle to emit to
    AstCFile* m_cfilep = nullptr;  // Current AstCFile being emitted
    std::vector<AstCFile*> m_newCfileps;  // AstCFiles created
    size_t m_splitSize = 0;  // Complexity of this file
    const size_t m_splitLimit = v3Global.opt.outputSplit()
                                    ? static_cast<size_t>(v3Global.opt.outputSplit())
                                    : std::numeric_limits<size_t>::max();

    // METHODS

    // Create new AstCFile and open it for writing
    void openNewOutputFile(const std::string& baseName, bool slow, bool support, bool source,
                           const char* const descriptionp) {
        std::string fileName = v3Global.opt.makeDir() + "/" + baseName;
        if (source) {
            if (slow) fileName += "__Slow";
            fileName += ".cpp";
        } else {
            fileName += ".h";
        }
        AstCFile* const cfilep = new AstCFile{v3Global.rootp()->fileline(), fileName};
        cfilep->slow(slow);
        cfilep->source(source);
        cfilep->support(support);
        m_newCfileps.emplace_back(cfilep);
        openOutputFile(cfilep, descriptionp);
    }

    // Reduce 'stmts' to a single statement, via a balanced tree of loose sub-functions
    // 'void <prefix>__<n>(<params>)' of at most 'maxCost' each (see emitSplitCtorDtor).
    // Returns the declaration of the root sub-function, or empty if nothing was split.
    std::string emitSplitTextStmts(TextStmts& stmts, const std::string& prefix,
                                   const std::string& params, const std::string& args,
                                   size_t maxCost, bool support, const char* descriptionp,
                                   const std::function<void()>& emitHeader);

public:
    // Create new source AstCFile and open it for writing
    void openNewOutputSourceFile(const std::string& baseName, bool slow, bool support,
                                 const char* descriptionp) {
        V3Stats::addStatSum(V3Stats::STAT_CPP_FILES, 1);
        openNewOutputFile(baseName, slow, support, true, descriptionp);
    }

    // Create new header AstCFile and open it for writing
    void openNewOutputHeaderFile(const std::string& baseName, const char* descriptionp) {
        openNewOutputFile(baseName, false, false, false, descriptionp);
    }

    // Open exisitng AstCFile for writing
    void openOutputFile(AstCFile* cfilep, const char* descriptionp) {
        UASSERT(!m_ofp, "Output file is already open");
        m_cfilep = cfilep;
        m_splitSize = 0;
        if (v3Global.opt.lintOnly()) {
            // Unfortunately we have some lint checks in EmitCImp, so we can't
            // just skip processing. TODO: Move them to an earlier stage.
            m_ofp = new V3OutCFile{VL_DEV_NULL};
            return;
        }
        m_ofp = new V3OutCFile{cfilep->name()};
        putsHeader();
        // Emit description
        m_ofp->putsNoTracking("// DESCR" /* keep this comment */ "IPTION: Verilator output: ");
        m_ofp->putsNoTracking(descriptionp);
        m_ofp->putsNoTracking("\n");
    }

    // Close current output file. Sets ofp() and outFileNodep() to nullptr.
    void closeOutputFile() {
        UASSERT(m_ofp, "No currently open output file");
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
        m_cfilep->complexityScore(m_splitSize);
        m_cfilep = nullptr;
    }

    std::vector<AstCFile*> getAndClearCfileps() {
        UASSERT(!m_ofp, "Output file is open");
        return std::move(m_newCfileps);
    }

    void splitSizeInc(size_t count) { m_splitSize += count; }
    void splitSizeInc(const AstNode* nodep) {
        splitSizeInc(static_cast<size_t>(nodep->nodeCount()));
    }
    bool splitNeeded(size_t splitLimit) const { return m_splitSize >= splitLimit; }
    bool splitNeeded() const { return splitNeeded(m_splitLimit); }

    // If the given constructor/destructor statements, plus 'baseCost', exceed the
    // --output-split-cfuncs limit, split them into loose sub-functions
    // 'void <prefix>__ctor__<n>(<params>)' and 'void <prefix>__dtor__<n>(<params>)', called
    // with '<args>'. Each is emitted into its own file, starting with 'emitHeader'. The
    // statements are then each replaced with a single call to the root sub-function. Returns
    // the declarations of the root ctor/dtor sub-functions, or empty strings if not split.
    std::pair<std::string, std::string>
    emitSplitCtorDtor(TextStmts& ctorStmts, TextStmts& dtorStmts, size_t baseCost,
                      const std::string& prefix, const std::string& params,
                      const std::string& args, bool support, const char* descriptionp,
                      const std::function<void()>& emitHeader);

    // Returns pointer to current output file object.
    V3OutCFile* ofp() const VL_MT_SAFE { return m_ofp; }

    void puts(const string& str) { ofp()->puts(str); }
    void putns(const AstNode* nodep, const string& str) { ofp()->putns(nodep, str); }
    void putsHeader() { ofp()->putsHeader(); }
    void putbs(const string& str) { ofp()->putbs(str); }
    void putnbs(const AstNode* nodep, const string& str) { ofp()->putnbs(nodep, str); }
    void putsDecoration(const AstNode* nodep, const string& str) {
        if (v3Global.opt.decoration()) putns(nodep, str);
    }
    void putsQuoted(const string& str) { ofp()->putsQuoted(str); }
    void ensureNewLine() { ofp()->ensureNewLine(); }
    bool optSystemC() { return v3Global.opt.systemC(); }
    static string protect(const string& name) VL_MT_SAFE { return VIdProtect::protect(name); }
    static string funcNameProtect(const AstCFunc* nodep, const AstNodeModule* modp = nullptr);
    static bool isExplicitlyConstructed(const AstVar* varp) VL_MT_STABLE {
        // Only model member variables may be handled explicitly
        const AstNodeModule* const modp = EmitCParentModule::get(varp);
        if (!modp || !varp->isModelState()) return false;
        // Classes use real constructors
        if (VN_IS(modp, Class)) return false;
        // Constant pool has special handling
        if (modp->isConstPool()) return false;
        // Otherwise explicitly handled if not trivially constructible,
        // meaning a runtime C++ constructor/destructor invocation is needed
        return !varp->isTriviallyConstructible();
    }
    // Name to access a module member as
    static std::string varName(const AstVar* varp) VL_MT_STABLE {
        const std::string name = varp->nameProtect();
        // Primary IOs live 'union { struct { HERE } __VprimaryPorts; }'
        if (varp->isPrimaryIO()) return "__VprimaryPorts." + name;
        // Explicitly constructed variables live 'union { struct { HERE } __Vnontrivs; }'
        if (isExplicitlyConstructed(varp)) return "__Vnontrivs." + name;
        // Otherwise they should be available in the local scope where emitted
        return name;
    }
    // Argument list; if 'cpp', C++ rather than a C header
    string cFuncArgs(const AstCFunc* nodep, bool cpp = true);
    void emitCDefaultConstructor(const AstNodeModule* modp);
    void emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp, bool withScope);
    void emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp, bool cLinkage = false);
    void emitVarDecl(const AstVar* nodep, bool asRef = false);
    void emitVarAccessors(const AstVar* nodep);
    template <typename T_Callable>
    static void forModCUse(const AstNodeModule* modp, VUseType useType, T_Callable action) {
        for (const AstNode* const itemp : modp->stmtspList()) {
            if (const AstCUse* const usep = VN_CAST(itemp, CUse)) {
                if (usep->useType().containsAny(useType)) {
                    if (usep->useType().containsAny(VUseType::INT_INCLUDE)) {
                        action("#include \"" + EmitCUtil::prefixNameProtect(usep) + ".h\"\n");
                        continue;  // Forward declaration is not necessary
                    }
                    if (usep->useType().containsAny(VUseType::INT_FWD_CLASS)) {
                        action("class " + EmitCUtil::prefixNameProtect(usep) + ";\n");
                    }
                }
            }
        }
    }
    void emitModCUse(const AstNodeModule* modp, VUseType useType);
    void emitSystemCSection(const AstNodeModule* modp, VSystemCSectionType type);
    static std::pair<string, FileLine*> scSection(const AstNodeModule* modp,
                                                  VSystemCSectionType type);

    // CONSTRUCTORS
    EmitCBaseVisitorConst() = default;
    ~EmitCBaseVisitorConst() override {
        UASSERT(!m_ofp, "Did not close output file");
        // Add files cerated to the netlist (unless retrieved before destruction)
        for (AstCFile* const cfilep : m_newCfileps) v3Global.rootp()->addFilesp(cfilep);
    }
};

#endif  // guard
