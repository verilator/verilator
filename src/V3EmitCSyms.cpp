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
#include "V3EmitCBase.h"
#include "V3Global.h"
#include "V3LanguageWords.h"
#include "V3PartitionGraph.h"

#include <algorithm>
#include <map>
#include <vector>

//######################################################################
// Symbol table emitting

class EmitCSyms final : EmitCBaseVisitor {
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1()  -> bool.  Set true __Vconfigure called
    const VNUser1InUse m_inuser1;

    // TYPES
    struct ScopeData {
        const string m_symName;
        const string m_prettyName;
        const int m_timeunit;
        string m_type;
        ScopeData(const string& symName, const string& prettyName, int timeunit,
                  const string& type)
            : m_symName{symName}
            , m_prettyName{prettyName}
            , m_timeunit{timeunit}
            , m_type{type} {}
    };
    struct ScopeFuncData {
        AstScopeName* const m_scopep;
        AstCFunc* const m_cfuncp;
        AstNodeModule* const m_modp;
        ScopeFuncData(AstScopeName* scopep, AstCFunc* funcp, AstNodeModule* modp)
            : m_scopep{scopep}
            , m_cfuncp{funcp}
            , m_modp{modp} {}
    };
    struct ScopeVarData {
        const string m_scopeName;
        const string m_varBasePretty;
        AstVar* const m_varp;
        const AstNodeModule* const m_modp;
        AstScope* const m_scopep;
        ScopeVarData(const string& scopeName, const string& varBasePretty, AstVar* varp,
                     const AstNodeModule* modp, AstScope* scopep)
            : m_scopeName{scopeName}
            , m_varBasePretty{varBasePretty}
            , m_varp{varp}
            , m_modp{modp}
            , m_scopep{scopep} {}
    };
    using ScopeNames = std::map<const std::string, ScopeData>;
    using ScopeModPair = std::pair<AstScope*, AstNodeModule*>;
    using ModVarPair = std::pair<AstNodeModule*, AstVar*>;
    using ScopeNameList = std::vector<std::string>;
    using ScopeNameHierarchy = std::map<const std::string, ScopeNameList>;
    struct CmpName {
        bool operator()(const ScopeModPair& lhsp, const ScopeModPair& rhsp) const {
            return lhsp.first->name() < rhsp.first->name();
        }
    };
    struct CmpDpi {
        bool operator()(const AstCFunc* lhsp, const AstCFunc* rhsp) const {
            if (lhsp->dpiImportPrototype() != rhsp->dpiImportPrototype()) {
                // cppcheck-suppress comparisonOfFuncReturningBoolError
                return lhsp->dpiImportPrototype() < rhsp->dpiImportPrototype();
            }
            return lhsp->name() < rhsp->name();
        }
    };

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // Current function
    AstNodeModule* m_modp = nullptr;  // Current module
    std::vector<ScopeModPair> m_scopes;  // Every scope by module
    std::vector<AstCFunc*> m_dpis;  // DPI functions
    std::vector<ModVarPair> m_modVars;  // Each public {mod,var}
    ScopeNames m_scopeNames;  // Each unique AstScopeName
    std::map<const std::string, ScopeFuncData> m_scopeFuncs;  // Each {scope,dpi-export-func}
    std::map<const std::string, ScopeVarData> m_scopeVars;  // Each {scope,public-var}
    ScopeNames m_vpiScopeCandidates;  // All scopes for VPI
    ScopeNameHierarchy m_vpiScopeHierarchy;  // The actual hierarchy of scopes
    int m_coverBins = 0;  // Coverage bin number
    const bool m_dpiHdrOnly;  // Only emit the DPI header
    int m_numStmts = 0;  // Number of statements output
    int m_funcNum = 0;  // CFunc split function number
    V3OutCFile* m_ofpBase = nullptr;  // Base (not split) C file
    std::unordered_map<int, bool> m_usesVfinal;  // Split method uses __Vfinal

    // METHODS
    void emitSymHdr();
    void checkSplit(bool usesVfinal);
    void closeSplit();
    void emitSymImpPreamble();
    void emitScopeHier(bool destroy);
    void emitSymImp();
    void emitDpiHdr();
    void emitDpiImp();

    static void nameCheck(AstNode* nodep) {
        // Prevent GCC compile time error; name check all things that reach C++ code
        if (nodep->name() != ""
            && !(VN_IS(nodep, CFunc)
                 && (VN_AS(nodep, CFunc)->isConstructor()
                     || VN_AS(nodep, CFunc)->isDestructor()))) {
            const string rsvd = V3LanguageWords::isKeyword(nodep->name());
            if (rsvd != "") {
                // Generally V3Name should find all of these and throw SYMRSVDWORD.
                // We'll still check here because the compiler errors
                // resulting if we miss this warning are SO nasty
                nodep->v3error("Symbol matching " + rsvd
                                   + " reserved word reached emitter,"
                                     " should have hit SYMRSVDWORD: "
                               << nodep->prettyNameQ());
            }
        }
    }

    static string scopeSymString(const string& scpname) {
        string out = scpname;
        string::size_type pos;
        while ((pos = out.find("__PVT__")) != string::npos) out.replace(pos, 7, "");
        if (out.substr(0, 10) == "TOP__DOT__") out.replace(0, 10, "");
        if (out.substr(0, 4) == "TOP.") out.replace(0, 4, "");
        while ((pos = out.find('.')) != string::npos) out.replace(pos, 1, "__");
        while ((pos = out.find("__DOT__")) != string::npos) out.replace(pos, 7, "__");
        return out;
    }

    static string scopeDecodeIdentifier(const string& scpname) {
        string out = scpname;
        // Remove hierarchy
        string::size_type pos = out.rfind('.');
        if (pos != std::string::npos) out.erase(0, pos + 1);
        // Decode all escaped characters
        while ((pos = out.find("__0")) != string::npos) {
            unsigned int x;
            std::stringstream ss;
            ss << std::hex << out.substr(pos + 3, 2);
            ss >> x;
            out.replace(pos, 5, 1, (char)x);
        }
        return out;
    }

    void varHierarchyScopes(string scp) {
        while (!scp.empty()) {
            const auto scpit = m_vpiScopeCandidates.find(scp);
            if ((scpit != m_vpiScopeCandidates.end())
                && (m_scopeNames.find(scp) == m_scopeNames.end())) {
                const auto scopeNameit = m_scopeNames.find(scpit->second.m_symName);
                if (scopeNameit == m_scopeNames.end()) {
                    m_scopeNames.emplace(scpit->second.m_symName, scpit->second);
                } else {
                    scopeNameit->second.m_type = scpit->second.m_type;
                }
            }
            string::size_type pos = scp.rfind("__DOT__");
            if (pos == string::npos) {
                pos = scp.rfind('.');
                if (pos == string::npos) break;
            }
            scp.resize(pos);
        }
    }

    void varsExpand() {
        // We didn't have all m_scopes loaded when we encountered variables, so expand them now
        // It would be less code if each module inserted its own variables.
        // Someday.  For now public isn't common.
        for (std::vector<ScopeModPair>::iterator itsc = m_scopes.begin(); itsc != m_scopes.end();
             ++itsc) {
            AstScope* const scopep = itsc->first;
            const AstNodeModule* const smodp = itsc->second;
            for (std::vector<ModVarPair>::iterator it = m_modVars.begin(); it != m_modVars.end();
                 ++it) {
                const AstNodeModule* const modp = it->first;
                AstVar* const varp = it->second;
                if (modp == smodp) {
                    // Need to split the module + var name into the
                    // original-ish full scope and variable name under that scope.
                    // The module instance name is included later, when we
                    // know the scopes this module is under
                    string whole = scopep->name() + "__DOT__" + varp->name();
                    string scpName;
                    string varBase;
                    if (whole.substr(0, 10) == "__DOT__TOP") whole.replace(0, 10, "");
                    const string::size_type dpos = whole.rfind("__DOT__");
                    if (dpos != string::npos) {
                        scpName = whole.substr(0, dpos);
                        varBase = whole.substr(dpos + strlen("__DOT__"));
                    } else {
                        varBase = whole;
                    }
                    // UINFO(9, "For " << scopep->name() << " - " << varp->name() << "  Scp "
                    // << scpName << "Var " << varBase << endl);
                    const string varBasePretty = AstNode::prettyName(varBase);
                    const string scpPretty = AstNode::prettyName(scpName);
                    const string scpSym = scopeSymString(scpName);
                    // UINFO(9, " scnameins sp " << scpName << " sp " << scpPretty << " ss "
                    // << scpSym << endl);
                    if (v3Global.opt.vpi()) varHierarchyScopes(scpName);
                    if (m_scopeNames.find(scpSym) == m_scopeNames.end()) {
                        m_scopeNames.insert(std::make_pair(
                            scpSym, ScopeData(scpSym, scpPretty, 0, "SCOPE_OTHER")));
                    }
                    m_scopeVars.insert(
                        std::make_pair(scpSym + " " + varp->name(),
                                       ScopeVarData(scpSym, varBasePretty, varp, modp, scopep)));
                }
            }
        }
    }

    void buildVpiHierarchy() {
        for (ScopeNames::const_iterator it = m_scopeNames.begin(); it != m_scopeNames.end();
             ++it) {
            if (it->second.m_type != "SCOPE_MODULE") continue;

            const string symName = it->second.m_symName;
            string above = symName;
            if (above.substr(0, 4) == "TOP.") above.replace(0, 4, "");

            while (!above.empty()) {
                const string::size_type pos = above.rfind("__");
                if (pos == string::npos) break;
                above.resize(pos);
                if (m_vpiScopeHierarchy.find(above) != m_vpiScopeHierarchy.end()) {
                    m_vpiScopeHierarchy[above].push_back(symName);
                    break;
                }
            }
            m_vpiScopeHierarchy[symName] = std::vector<string>();
        }
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        // Collect list of scopes
        iterateChildren(nodep);
        varsExpand();

        if (v3Global.opt.vpi()) buildVpiHierarchy();

        // Sort by names, so line/process order matters less
        stable_sort(m_scopes.begin(), m_scopes.end(), CmpName());
        stable_sort(m_dpis.begin(), m_dpis.end(), CmpDpi());

        // Output
        if (!m_dpiHdrOnly) {
            // Must emit implementation first to determine number of splits
            emitSymImp();
            emitSymHdr();
        }
        if (v3Global.dpi()) {
            emitDpiHdr();
            if (!m_dpiHdrOnly) emitDpiImp();
        }
    }
    virtual void visit(AstConstPool* nodep) override {}  // Ignore
    virtual void visit(AstNodeModule* nodep) override {
        nameCheck(nodep);
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstCellInline* nodep) override {
        if (v3Global.opt.vpi()) {
            const string type
                = (nodep->origModName() == "__BEGIN__") ? "SCOPE_OTHER" : "SCOPE_MODULE";
            const string name = nodep->scopep()->name() + "__DOT__" + nodep->name();
            const string name_dedot = AstNode::dedotName(name);
            const int timeunit = m_modp->timeunit().powerOfTen();
            m_vpiScopeCandidates.insert(
                std::make_pair(name, ScopeData(scopeSymString(name), name_dedot, timeunit, type)));
        }
    }
    virtual void visit(AstScope* nodep) override {
        if (VN_IS(m_modp, Class)) return;  // The ClassPackage is what is visible
        nameCheck(nodep);

        m_scopes.emplace_back(std::make_pair(nodep, m_modp));

        if (v3Global.opt.vpi() && !nodep->isTop()) {
            const string type = VN_IS(nodep->modp(), Package) ? "SCOPE_OTHER" : "SCOPE_MODULE";
            const string name_dedot = AstNode::dedotName(nodep->shortName());
            const int timeunit = m_modp->timeunit().powerOfTen();
            m_vpiScopeCandidates.insert(
                std::make_pair(nodep->name(), ScopeData(scopeSymString(nodep->name()), name_dedot,
                                                        timeunit, type)));
        }
    }
    virtual void visit(AstScopeName* nodep) override {
        const string name = nodep->scopeSymName();
        // UINFO(9,"scnameins sp "<<nodep->name()<<" sp "<<nodep->scopePrettySymName()
        // <<" ss"<<name<<endl);
        const int timeunit = m_modp ? m_modp->timeunit().powerOfTen() : 0;
        if (m_scopeNames.find(name) == m_scopeNames.end()) {
            m_scopeNames.emplace(
                name, ScopeData(name, nodep->scopePrettySymName(), timeunit, "SCOPE_OTHER"));
        }
        if (nodep->dpiExport()) {
            UASSERT_OBJ(m_cfuncp, nodep, "ScopeName not under DPI function");
            m_scopeFuncs.insert(std::make_pair(name + " " + m_cfuncp->name(),
                                               ScopeFuncData(nodep, m_cfuncp, m_modp)));
        } else {
            if (m_scopeNames.find(nodep->scopeDpiName()) == m_scopeNames.end()) {
                m_scopeNames.insert(
                    std::make_pair(nodep->scopeDpiName(),
                                   ScopeData(nodep->scopeDpiName(), nodep->scopePrettyDpiName(),
                                             timeunit, "SCOPE_OTHER")));
            }
        }
    }
    virtual void visit(AstVar* nodep) override {
        nameCheck(nodep);
        iterateChildren(nodep);
        if (nodep->isSigUserRdPublic() && !m_cfuncp)
            m_modVars.emplace_back(std::make_pair(m_modp, nodep));
    }
    virtual void visit(AstCoverDecl* nodep) override {
        // Assign numbers to all bins, so we know how big of an array to use
        if (!nodep->dataDeclNullp()) {  // else duplicate we don't need code for
            nodep->binNum(m_coverBins++);
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        nameCheck(nodep);
        if (nodep->dpiImportPrototype() || nodep->dpiExportDispatcher()) m_dpis.push_back(nodep);
        VL_RESTORER(m_cfuncp);
        {
            m_cfuncp = nodep;
            iterateChildren(nodep);
        }
    }

    //---------------------------------------
    virtual void visit(AstConst*) override {}
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit EmitCSyms(AstNetlist* nodep, bool dpiHdrOnly)
        : m_dpiHdrOnly{dpiHdrOnly} {
        iterate(nodep);
    }
};

void EmitCSyms::emitSymHdr() {
    UINFO(6, __FUNCTION__ << ": " << endl);
    const string filename = v3Global.opt.makeDir() + "/" + symClassName() + ".h";
    newCFile(filename, true /*slow*/, false /*source*/);

    if (v3Global.opt.systemC()) {
        m_ofp = new V3OutScFile(filename);
    } else {
        m_ofp = new V3OutCFile(filename);
    }

    ofp()->putsHeader();
    puts("// DESCRIPTION: Verilator output: Symbol table internal header\n");
    puts("//\n");
    puts("// Internal details; most calling programs do not need this header,\n");
    puts("// unless using verilator public meta comments.\n");

    ofp()->putsGuard();

    puts("\n");
    ofp()->putsIntTopInclude();
    puts("#include \"verilated.h\"\n");
    if (v3Global.needTraceDumper()) {
        puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
    }
    if (v3Global.opt.usesProfiler()) puts("#include \"verilated_profiler.h\"\n");

    puts("\n// INCLUDE MODEL CLASS\n");
    puts("\n#include \"" + topClassName() + ".h\"\n");

    puts("\n// INCLUDE MODULE CLASSES\n");
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_AS(nodep->nextp(), NodeModule)) {
        if (VN_IS(nodep, Class)) continue;  // Class included earlier
        puts("#include \"" + prefixNameProtect(nodep) + ".h\"\n");
    }

    if (v3Global.dpi()) {
        puts("\n// DPI TYPES for DPI Export callbacks (Internal use)\n");
        std::map<const string, int> types;  // Remove duplicates and sort
        for (const auto& itr : m_scopeFuncs) {
            const AstCFunc* const funcp = itr.second.m_cfuncp;
            if (funcp->dpiExportImpl()) {
                const string cbtype
                    = protect(v3Global.opt.prefix() + "__Vcb_" + funcp->cname() + "_t");
                types["using " + cbtype + " = void (*) (" + cFuncArgs(funcp) + ");\n"] = 1;
            }
        }
        for (const auto& i : types) puts(i.first);
    }

    puts("\n// SYMS CLASS (contains all model state)\n");
    puts("class " + symClassName() + " final : public VerilatedSyms {\n");
    ofp()->putsPrivate(false);  // public:

    puts("// INTERNAL STATE\n");
    puts(topClassName() + "* const __Vm_modelp;\n");

    if (v3Global.needTraceDumper()) {
        // __Vm_dumperp is local, otherwise we wouldn't know what design's eval()
        // should call a global dumpperp
        puts("bool __Vm_dumping = false;  // Dumping is active\n");
        puts("VerilatedMutex __Vm_dumperMutex;  // Protect __Vm_dumperp\n");
        puts(v3Global.opt.traceClassLang()
             + "* __Vm_dumperp VL_GUARDED_BY(__Vm_dumperMutex) = nullptr;"
               "  /// Trace class for $dump*\n");
    }
    if (v3Global.opt.trace()) {
        puts("bool __Vm_activity = false;"
             "  ///< Used by trace routines to determine change occurred\n");
        puts("uint32_t __Vm_baseCode = 0;"
             "  ///< Used by trace routines when tracing multiple models\n");
    }
    puts("bool __Vm_didInit = false;\n");

    if (v3Global.opt.mtasks()) {
        puts("\n// MULTI-THREADING\n");
        puts("VlThreadPool* const __Vm_threadPoolp;\n");
        puts("bool __Vm_even_cycle = false;\n");
    }

    if (v3Global.opt.profExec()) {
        puts("\n// EXECUTION PROFILING\n");
        puts("VlExecutionProfiler* const __Vm_executionProfilerp;\n");
    }

    puts("\n// MODULE INSTANCE STATE\n");
    for (const auto& i : m_scopes) {
        const AstScope* const scopep = i.first;
        const AstNodeModule* const modp = i.second;
        if (VN_IS(modp, Class)) continue;
        const string name = prefixNameProtect(modp);
        ofp()->printf("%-30s ", name.c_str());
        puts(protectIf(scopep->nameDotless(), scopep->protect()) + ";\n");
    }

    if (m_coverBins) {
        puts("\n// COVERAGE\n");
        puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
        puts(" __Vcoverage[");
        puts(cvtToStr(m_coverBins));
        puts("];\n");
    }

    if (v3Global.opt.profPgo()) {
        puts("\n// PGO PROFILING\n");
        const uint32_t usedMTaskProfilingIDs = v3Global.rootp()->usedMTaskProfilingIDs();
        puts("VlPgoProfiler<" + cvtToStr(usedMTaskProfilingIDs) + "> _vm_pgoProfiler;\n");
    }

    if (!m_scopeNames.empty()) {  // Scope names
        puts("\n// SCOPE NAMES\n");
        for (const auto& itr : m_scopeNames) {
            puts("VerilatedScope " + protect("__Vscope_" + itr.second.m_symName) + ";\n");
        }
    }

    if (v3Global.opt.vpi()) {
        puts("\n// SCOPE HIERARCHY\n");
        puts("VerilatedHierarchy __Vhier;\n");
    }

    puts("\n// CONSTRUCTORS\n");
    puts(symClassName() + "(VerilatedContext* contextp, const char* namep, " + topClassName()
         + "* modelp);\n");
    puts(string("~") + symClassName() + "();\n");

    for (const auto& i : m_usesVfinal) {
        puts("void " + symClassName() + "_" + cvtToStr(i.first) + "(");
        if (i.second) { puts("int __Vfinal"); }
        puts(");\n");
    }

    puts("\n// METHODS\n");
    puts("const char* name() { return TOP.name(); }\n");

    if (v3Global.needTraceDumper()) {
        if (!optSystemC()) puts("void _traceDump();\n");
        puts("void _traceDumpOpen();\n");
        puts("void _traceDumpClose();\n");
    }

    if (v3Global.opt.savable()) {
        puts("void " + protect("__Vserialize") + "(VerilatedSerialize& os);\n");
        puts("void " + protect("__Vdeserialize") + "(VerilatedDeserialize& os);\n");
    }
    puts("} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);\n");

    ofp()->putsEndGuard();
    VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
}

void EmitCSyms::closeSplit() {
    if (!m_ofp || m_ofp == m_ofpBase) return;

    puts("}\n");
    VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
}

void EmitCSyms::checkSplit(bool usesVfinal) {
    if (m_ofp
        && (!v3Global.opt.outputSplitCFuncs() || m_numStmts < v3Global.opt.outputSplitCFuncs())) {
        return;
    }

    // Splitting file, so using parallel build.
    v3Global.useParallelBuild(true);

    m_numStmts = 0;
    const string filename
        = v3Global.opt.makeDir() + "/" + symClassName() + "__" + cvtToStr(++m_funcNum) + ".cpp";
    AstCFile* const cfilep = newCFile(filename, true /*slow*/, true /*source*/);
    cfilep->support(true);
    m_usesVfinal[m_funcNum] = usesVfinal;
    closeSplit();

    if (v3Global.opt.systemC()) {
        m_ofp = new V3OutScFile(filename);
    } else {
        m_ofp = new V3OutCFile(filename);
    }

    m_ofpBase->puts(symClassName() + "_" + cvtToStr(m_funcNum) + "(");
    if (usesVfinal) { m_ofpBase->puts("__Vfinal"); }
    m_ofpBase->puts(");\n");

    emitSymImpPreamble();
    puts("void " + symClassName() + "::" + symClassName() + "_" + cvtToStr(m_funcNum) + "(");
    if (usesVfinal) { puts("int __Vfinal"); }
    puts(") {\n");
}

void EmitCSyms::emitSymImpPreamble() {
    ofp()->putsHeader();
    puts("// DESCR"
         "IPTION: Verilator output: Symbol table implementation internals\n");
    puts("\n");

    // Includes
    puts("#include \"" + symClassName() + ".h\"\n");
    puts("#include \"" + topClassName() + ".h\"\n");
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_AS(nodep->nextp(), NodeModule)) {
        if (VN_IS(nodep, Class)) continue;  // Class included earlier
        puts("#include \"" + prefixNameProtect(nodep) + ".h\"\n");
    }
    puts("\n");
    // Declarations for DPI Export implementation functions
    bool needsNewLine = false;
    for (const auto& pair : m_scopeFuncs) {
        const AstCFunc* const funcp = pair.second.m_cfuncp;
        if (!funcp->dpiExportImpl()) continue;
        emitCFuncDecl(funcp, pair.second.m_modp);
        needsNewLine = true;
    }
    if (needsNewLine) puts("\n");
}

void EmitCSyms::emitScopeHier(bool destroy) {
    if (v3Global.opt.vpi()) {
        const string verb = destroy ? "Tear down" : "Set up";
        const string method = destroy ? "remove" : "add";
        puts("\n// " + verb + " scope hierarchy\n");
        for (ScopeNames::const_iterator it = m_scopeNames.begin(); it != m_scopeNames.end();
             ++it) {
            const string name = it->second.m_prettyName;
            if (it->first == "TOP") continue;
            if ((name.find('.') == string::npos) && (it->second.m_type == "SCOPE_MODULE")) {
                puts("__Vhier." + method + "(0, &" + protect("__Vscope_" + it->second.m_symName)
                     + ");\n");
            }
        }

        for (auto it = m_vpiScopeHierarchy.cbegin(); it != m_vpiScopeHierarchy.cend(); ++it) {
            for (ScopeNameList::const_iterator lit = it->second.begin(); lit != it->second.end();
                 ++lit) {
                const string fromname = scopeSymString(it->first);
                const string toname = scopeSymString(*lit);
                const auto from = vlstd::as_const(m_scopeNames).find(fromname);
                const auto to = vlstd::as_const(m_scopeNames).find(toname);
                UASSERT(from != m_scopeNames.end(), fromname + " not in m_scopeNames");
                UASSERT(to != m_scopeNames.end(), toname + " not in m_scopeNames");
                puts("__Vhier." + method + "(");
                puts("&" + protect("__Vscope_" + from->second.m_symName) + ", ");
                puts("&" + protect("__Vscope_" + to->second.m_symName) + ");\n");
            }
        }
        puts("\n");
    }
}

void EmitCSyms::emitSymImp() {
    UINFO(6, __FUNCTION__ << ": " << endl);
    const string filename = v3Global.opt.makeDir() + "/" + symClassName() + ".cpp";
    AstCFile* const cfilep = newCFile(filename, true /*slow*/, true /*source*/);
    cfilep->support(true);

    if (v3Global.opt.systemC()) {
        m_ofp = new V3OutScFile(filename);
    } else {
        m_ofp = new V3OutCFile(filename);
    }

    m_ofpBase = m_ofp;
    emitSymImpPreamble();

    if (v3Global.opt.savable()) {
        for (const bool& de : {false, true}) {
            const string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
            const string funcname = de ? "__Vdeserialize" : "__Vserialize";
            const string op = de ? ">>" : "<<";
            // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
            puts("void " + symClassName() + "::" + protect(funcname) + "(" + classname
                 + "& os) {\n");
            puts("// Internal state\n");
            if (v3Global.opt.trace()) puts("os" + op + "__Vm_activity;\n");
            puts("os " + op + " __Vm_didInit;\n");
            puts("// Module instance state\n");
            for (const auto& pair : m_scopes) {
                const AstScope* const scopep = pair.first;
                puts(protectIf(scopep->nameDotless(), scopep->protect()) + "." + protect(funcname)
                     + "(os);\n");
            }
            puts("}\n");
        }
        puts("\n");
    }

    puts("// FUNCTIONS\n");

    // Destructor
    puts(symClassName() + "::~" + symClassName() + "()\n");
    puts("{\n");
    emitScopeHier(true);
    if (v3Global.needTraceDumper()) {
        puts("#ifdef VM_TRACE\n");
        puts("if (__Vm_dumping) _traceDumpClose();\n");
        puts("#endif  // VM_TRACE\n");
    }
    if (v3Global.opt.profPgo()) {
        puts("_vm_pgoProfiler.write(\"" + topClassName()
             + "\", _vm_contextp__->profVltFilename());\n");
    }
    puts("}\n");

    if (v3Global.needTraceDumper()) {
        if (!optSystemC()) {
            puts("\nvoid " + symClassName() + "::_traceDump() {\n");
            // Caller checked for __Vm_dumperp non-nullptr
            puts("const VerilatedLockGuard lock(__Vm_dumperMutex);\n");
            puts("__Vm_dumperp->dump(VL_TIME_Q());\n");
            puts("}\n");
        }

        puts("\nvoid " + symClassName() + "::_traceDumpOpen() {\n");
        puts("const VerilatedLockGuard lock(__Vm_dumperMutex);\n");
        puts("if (VL_UNLIKELY(!__Vm_dumperp)) {\n");
        puts("__Vm_dumperp = new " + v3Global.opt.traceClassLang() + "();\n");
        puts("__Vm_modelp->trace(__Vm_dumperp, 0, 0);\n");
        puts("std::string dumpfile = _vm_contextp__->dumpfileCheck();\n");
        puts("__Vm_dumperp->open(dumpfile.c_str());\n");
        puts("__Vm_dumping = true;\n");
        puts("}\n");
        puts("}\n");

        puts("\nvoid " + symClassName() + "::_traceDumpClose() {\n");
        puts("const VerilatedLockGuard lock(__Vm_dumperMutex);\n");
        puts("__Vm_dumping = false;\n");
        puts("VL_DO_CLEAR(delete __Vm_dumperp, __Vm_dumperp = nullptr);\n");
        puts("}\n");
    }
    puts("\n");

    // Constructor
    puts(symClassName() + "::" + symClassName()
         + "(VerilatedContext* contextp, const char* namep, " + topClassName() + "* modelp)\n");
    puts("    : VerilatedSyms{contextp}\n");
    puts("    // Setup internal state of the Syms class\n");
    puts("    , __Vm_modelp{modelp}\n");

    if (v3Global.opt.mtasks()) {
        // TODO -- For now each model creates its own ThreadPool here,
        // and deletes it in the destructor. If A and B are each top level
        // modules, each creates a separate thread pool.  This allows
        // A.eval() and B.eval() to run concurrently without any
        // interference -- so long as the physical machine has enough cores
        // to support both pools and all testbench threads.
        //
        // In the future, we might want to let the client provide a
        // threadpool to the constructor. This would allow two or more
        // models to share a single threadpool.
        //
        // For example: suppose models A and B are each compiled to run on
        // 4 threads. The client might create a single thread pool with 3
        // threads and pass it to both models. If the client can ensure that
        // A.eval() and B.eval() do NOT run concurrently, there will be no
        // contention for the threads. This mode is missing for now.  (Is
        // there demand for such a setup?)
        //
        // Note we create N-1 threads in the thread pool. The thread
        // that calls eval() becomes the final Nth thread for the
        // duration of the eval call.
        puts("    , __Vm_threadPoolp{static_cast<VlThreadPool*>(contextp->threadPoolp())}\n");
    }

    if (v3Global.opt.profExec()) {
        puts("    , "
             "__Vm_executionProfilerp{static_cast<VlExecutionProfiler*>(contextp->"
             "enableExecutionProfiler(&VlExecutionProfiler::construct))}\n");
    }

    puts("    // Setup module instances\n");
    for (const auto& i : m_scopes) {
        const AstScope* const scopep = i.first;
        const AstNodeModule* const modp = i.second;
        puts("    , ");
        puts(protect(scopep->nameDotless()));
        puts("{this");
        if (modp->isTop()) {
            puts(", namep");
        } else {
            // The "." is added by catName
            puts(", Verilated::catName(namep, ");
            putsQuoted(protectWordsIf(scopep->prettyName(), scopep->protect()));
            puts(")");
        }
        puts("}\n");
        ++m_numStmts;
    }
    puts("{\n");

    if (v3Global.opt.profPgo()) {
        puts("// Configure profiling for PGO\n");
        if (v3Global.opt.mtasks()) {
            v3Global.rootp()->topModulep()->foreach<AstExecGraph>(
                [&](const AstExecGraph* execGraphp) {
                    for (const V3GraphVertex* vxp = execGraphp->depGraphp()->verticesBeginp(); vxp;
                         vxp = vxp->verticesNextp()) {
                        const ExecMTask* const mtp = static_cast<const ExecMTask*>(vxp);
                        puts("_vm_pgoProfiler.addCounter(" + cvtToStr(mtp->profilerId()) + ", \""
                             + mtp->hashName() + "\");\n");
                    }
                });
        }
    }

    puts("// Configure time unit / time precision\n");
    if (!v3Global.rootp()->timeunit().isNone()) {
        puts("_vm_contextp__->timeunit(");
        puts(cvtToStr(v3Global.rootp()->timeunit().powerOfTen()));
        puts(");\n");
    }
    if (!v3Global.rootp()->timeprecision().isNone()) {
        puts("_vm_contextp__->timeprecision(");
        puts(cvtToStr(v3Global.rootp()->timeprecision().powerOfTen()));
        puts(");\n");
    }

    puts("// Setup each module's pointers to their submodules\n");
    for (const auto& i : m_scopes) {
        const AstScope* const scopep = i.first;
        const AstNodeModule* const modp = i.second;
        if (const AstScope* const aboveScopep = scopep->aboveScopep()) {
            checkSplit(false);
            const string protName = protectWordsIf(scopep->name(), scopep->protect());
            if (VN_IS(modp, ClassPackage)) {
                // ClassPackage modules seem to be a bit out of place, so hard code...
                puts("TOP");
            } else {
                puts(protectIf(aboveScopep->nameDotless(), aboveScopep->protect()));
            }
            puts(".");
            puts(protName.substr(protName.rfind('.') + 1));
            puts(" = &");
            puts(protectIf(scopep->nameDotless(), scopep->protect()) + ";\n");
            ++m_numStmts;
        }
    }

    puts("// Setup each module's pointer back to symbol table (for public functions)\n");
    for (const auto& i : m_scopes) {
        AstScope* const scopep = i.first;
        AstNodeModule* const modp = i.second;
        checkSplit(false);
        // first is used by AstCoverDecl's call to __vlCoverInsert
        const bool first = !modp->user1();
        modp->user1(true);
        puts(protectIf(scopep->nameDotless(), scopep->protect()) + "." + protect("__Vconfigure")
             + "(" + (first ? "true" : "false") + ");\n");
        ++m_numStmts;
    }

    if (!m_scopeNames.empty()) {  // Setup scope names
        puts("// Setup scopes\n");
        for (ScopeNames::iterator it = m_scopeNames.begin(); it != m_scopeNames.end(); ++it) {
            checkSplit(false);
            puts(protect("__Vscope_" + it->second.m_symName) + ".configure(this, name(), ");
            putsQuoted(protectWordsIf(it->second.m_prettyName, true));
            puts(", ");
            putsQuoted(protect(scopeDecodeIdentifier(it->second.m_prettyName)));
            puts(", ");
            puts(cvtToStr(it->second.m_timeunit));
            puts(", VerilatedScope::" + it->second.m_type + ");\n");
            ++m_numStmts;
        }
    }

    emitScopeHier(false);

    // Everything past here is in the __Vfinal loop, so start a new split file if needed
    closeSplit();

    if (v3Global.dpi()) {
        m_ofpBase->puts("// Setup export functions\n");
        m_ofpBase->puts("for (int __Vfinal=0; __Vfinal<2; __Vfinal++) {\n");
        for (auto it = m_scopeFuncs.begin(); it != m_scopeFuncs.end(); ++it) {
            AstScopeName* const scopep = it->second.m_scopep;
            AstCFunc* const funcp = it->second.m_cfuncp;
            AstNodeModule* const modp = it->second.m_modp;
            if (funcp->dpiExportImpl()) {
                checkSplit(true);
                puts(protect("__Vscope_" + scopep->scopeSymName()) + ".exportInsert(__Vfinal, ");
                putsQuoted(funcp->cname());  // Not protected - user asked for import/export
                puts(", (void*)(&");
                puts(prefixNameProtect(modp));
                puts("__");
                puts(funcp->nameProtect());
                puts("));\n");
                ++m_numStmts;
            }
        }
        // It would be less code if each module inserted its own variables.
        // Someday.  For now public isn't common.
        for (auto it = m_scopeVars.begin(); it != m_scopeVars.end(); ++it) {
            checkSplit(true);
            AstScope* const scopep = it->second.m_scopep;
            AstVar* const varp = it->second.m_varp;
            //
            int pwidth = 1;
            int pdim = 0;
            int udim = 0;
            string bounds;
            if (AstBasicDType* const basicp = varp->basicp()) {
                // Range is always first, it's not in "C" order
                if (basicp->isRanged()) {
                    bounds += " ,";
                    bounds += cvtToStr(basicp->hi());
                    bounds += ",";
                    bounds += cvtToStr(basicp->lo());
                    pdim++;
                    pwidth *= basicp->elements();
                }
                for (AstNodeDType* dtypep = varp->dtypep(); dtypep;) {
                    dtypep
                        = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
                    if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                        bounds += " ,";
                        bounds += cvtToStr(adtypep->left());
                        bounds += ",";
                        bounds += cvtToStr(adtypep->right());
                        if (VN_IS(dtypep, PackArrayDType)) {
                            pdim++;
                            pwidth *= adtypep->elementsConst();
                        } else {
                            udim++;
                        }
                        dtypep = adtypep->subDTypep();
                    } else {
                        break;  // AstBasicDType - nothing below, 1
                    }
                }
            }
            // TODO: actually expose packed arrays as vpiRegArray
            if (pdim > 1 && udim == 0) {
                bounds = ", ";
                bounds += cvtToStr(pwidth - 1);
                bounds += ",0";
                pdim = 1;
            }
            if (pdim > 1 || udim > 1) {
                puts("//UNSUP ");  // VerilatedImp can't deal with >2d or packed arrays
            }
            puts(protect("__Vscope_" + it->second.m_scopeName) + ".varInsert(__Vfinal,");
            putsQuoted(protect(it->second.m_varBasePretty));

            std::string varName;
            varName += protectIf(scopep->nameDotless(), scopep->protect()) + ".";
            varName += protect(varp->name());

            if (varp->isParam()) {
                if (varp->vlEnumType() == "VLVT_STRING") {
                    puts(", const_cast<void*>(static_cast<const void*>(");
                    puts(varName);
                    puts(".c_str())), ");
                } else {
                    puts(", const_cast<void*>(static_cast<const void*>(&(");
                    puts(varName);
                    puts("))), ");
                }
            } else {
                puts(", &(");
                puts(varName);
                puts("), ");
            }

            puts(varp->isParam() ? "true" : "false");
            puts(", ");
            puts(varp->vlEnumType());  // VLVT_UINT32 etc
            puts(",");
            puts(varp->vlEnumDir());  // VLVD_IN etc
            puts(",");
            puts(cvtToStr(pdim + udim));
            puts(bounds);
            puts(");\n");
            ++m_numStmts;
        }
        m_ofpBase->puts("}\n");
    }

    m_ofpBase->puts("}\n");

    closeSplit();
    m_ofp = nullptr;
    VL_DO_CLEAR(delete m_ofpBase, m_ofpBase = nullptr);
}

//######################################################################

void EmitCSyms::emitDpiHdr() {
    UINFO(6, __FUNCTION__ << ": " << endl);
    const string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__Dpi.h";
    AstCFile* const cfilep = newCFile(filename, false /*slow*/, false /*source*/);
    cfilep->support(true);
    V3OutCFile hf(filename);
    m_ofp = &hf;

    m_ofp->putsHeader();
    puts("// DESCR"
         "IPTION: Verilator output: Prototypes for DPI import and export functions.\n");
    puts("//\n");
    puts("// Verilator includes this file in all generated .cpp files that use DPI functions.\n");
    puts("// Manually include this file where DPI .c import functions are declared to ensure\n");
    puts("// the C functions match the expectations of the DPI imports.\n");

    ofp()->putsGuard();

    puts("\n");
    puts("#include \"svdpi.h\"\n");
    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("extern \"C\" {\n");
    puts("#endif\n");
    puts("\n");

    int firstExp = 0;
    int firstImp = 0;
    for (AstCFunc* nodep : m_dpis) {
        if (nodep->dpiExportDispatcher()) {
            if (!firstExp++) puts("\n// DPI EXPORTS\n");
            putsDecoration("// DPI export" + ifNoProtect(" at " + nodep->fileline()->ascii())
                           + "\n");
            puts("extern " + nodep->rtnTypeVoid() + " " + nodep->nameProtect() + "("
                 + cFuncArgs(nodep) + ");\n");
        } else if (nodep->dpiImportPrototype()) {
            if (!firstImp++) puts("\n// DPI IMPORTS\n");
            putsDecoration("// DPI import" + ifNoProtect(" at " + nodep->fileline()->ascii())
                           + "\n");
            puts("extern " + nodep->rtnTypeVoid() + " " + nodep->nameProtect() + "("
                 + cFuncArgs(nodep) + ");\n");
        }
    }

    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("}\n");
    puts("#endif\n");

    ofp()->putsEndGuard();
}

//######################################################################

void EmitCSyms::emitDpiImp() {
    UINFO(6, __FUNCTION__ << ": " << endl);
    const string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__Dpi.cpp";
    AstCFile* const cfilep = newCFile(filename, false /*slow*/, true /*source*/);
    cfilep->support(true);
    V3OutCFile hf(filename);
    m_ofp = &hf;

    m_ofp->putsHeader();
    puts("// DESCR"
         "IPTION: Verilator output: Implementation of DPI export functions.\n");
    puts("//\n");
    puts("// Verilator compiles this file in when DPI functions are used.\n");
    puts("// If you have multiple Verilated designs with the same DPI exported\n");
    puts("// function names, you will get multiple definition link errors from here.\n");
    puts("// This is an unfortunate result of the DPI specification.\n");
    puts("// To solve this, either\n");
    puts("//    1. Call " + topClassName() + "::{export_function} instead,\n");
    puts("//       and do not even bother to compile this file\n");
    puts("// or 2. Compile all __Dpi.cpp files in the same compiler run,\n");
    puts("//       and #ifdefs already inserted here will sort everything out.\n");
    puts("\n");

    puts("#include \"" + topClassName() + "__Dpi.h\"\n");
    puts("#include \"" + topClassName() + ".h\"\n");
    puts("\n");

    for (AstCFunc* nodep : m_dpis) {
        if (nodep->dpiExportDispatcher()) {
            // Prevent multi-definition if used by multiple models
            puts("#ifndef VL_DPIDECL_" + nodep->name() + "_\n");
            puts("#define VL_DPIDECL_" + nodep->name() + "_\n");
            puts(nodep->rtnTypeVoid() + " " + nodep->name() + "(" + cFuncArgs(nodep) + ") {\n");
            puts("// DPI export" + ifNoProtect(" at " + nodep->fileline()->ascii()) + "\n");
            puts("return " + topClassName() + "::" + nodep->name() + "(");
            string args;
            for (AstNode* stmtp = nodep->argsp(); stmtp; stmtp = stmtp->nextp()) {
                if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
                    if (portp->isIO() && !portp->isFuncReturn()) {
                        if (args != "") args += ", ";
                        args += portp->name();
                    }
                }
            }
            puts(args + ");\n");
            puts("}\n");
            puts("#endif\n");
            puts("\n");
        }
    }
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcSyms(bool dpiHdrOnly) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCSyms(v3Global.rootp(), dpiHdrOnly);
}
