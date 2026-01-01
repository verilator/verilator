// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3ExecGraph.h"
#include "V3LanguageWords.h"
#include "V3StackCount.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Symbol table emitting

// Some handy short-hands to reduce verbosity
static constexpr auto symClassName = &EmitCUtil::symClassName;
static constexpr auto topClassName = &EmitCUtil::topClassName;

class EmitCSyms final : EmitCBaseVisitorConst {
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1()  -> bool.  Set true __Vconfigure called
    const VNUser1InUse m_inuser1;

    // TYPES
    struct ScopeData final {
        const AstNode* m_nodep;
        const std::string m_symName;
        const std::string m_prettyName;
        const std::string m_defName;
        const int m_timeunit;
        std::string m_type;  // TODO: this should be an enum
        ScopeData(const AstNode* nodep, const std::string& symName, const std::string& prettyName,
                  const std::string& defName, int timeunit, const std::string& type)
            : m_nodep{nodep}
            , m_symName{symName}
            , m_prettyName{prettyName}
            , m_defName{defName}
            , m_timeunit{timeunit}
            , m_type{type} {}
    };
    struct ScopeFuncData final {
        const AstScopeName* const m_scopep;
        const AstCFunc* const m_cfuncp;
        const AstNodeModule* const m_modp;
        ScopeFuncData(const AstScopeName* scopep, const AstCFunc* funcp, const AstNodeModule* modp)
            : m_scopep{scopep}
            , m_cfuncp{funcp}
            , m_modp{modp} {}
    };
    struct ScopeVarData final {
        const std::string m_scopeName;
        const std::string m_varBasePretty;
        const AstVar* const m_varp;
        const AstNodeModule* const m_modp;
        const AstScope* const m_scopep;
        ScopeVarData(const std::string& scopeName, const std::string& varBasePretty,
                     const AstVar* varp, const AstNodeModule* modp, const AstScope* scopep)
            : m_scopeName{scopeName}
            , m_varBasePretty{varBasePretty}
            , m_varp{varp}
            , m_modp{modp}
            , m_scopep{scopep} {}
    };
    using ScopeNames = std::map<const std::string, ScopeData>;
    using ScopeModPair = std::pair<const AstScope*, AstNodeModule*>;
    using ModVarPair = std::pair<const AstNodeModule*, const AstVar*>;

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // Current function
    AstNodeModule* m_modp = nullptr;  // Current module
    std::vector<ScopeModPair> m_scopes;  // Every scope by module
    std::vector<AstCFunc*> m_dpis;  // DPI functions
    std::vector<ModVarPair> m_modVars;  // Each public {mod,var}
    std::map<const std::string, ScopeFuncData> m_scopeFuncs;  // Each {scope,dpi-export-func}
    std::map<const std::string, ScopeVarData> m_scopeVars;  // Each {scope,public-var}
    ScopeNames m_scopeNames;  // Each unique AstScopeName. Dpi scopes added later
    ScopeNames m_dpiScopeNames;  // Each unique AstScopeName for DPI export
    ScopeNames m_vpiScopeCandidates;  // All scopes for VPI
    // The actual hierarchy of scopes
    std::map<const std::string, std::vector<std::string>> m_vpiScopeHierarchy;
    int m_coverBins = 0;  // Coverage bin number
    const bool m_dpiHdrOnly;  // Only emit the DPI header
    std::vector<std::string> m_splitFuncNames;  // Split file names
    VDouble0 m_statVarScopeBytes;  // Statistic tracking

    // METHODS
    void emitSymHdr();
    void emitSymImpPreamble();
    void emitScopeHier(std::vector<std::string>& stmts, bool destroy);
    void emitSymImp(const AstNetlist* netlistp);
    void emitDpiHdr();
    void emitDpiImp();

    void emitSplit(std::vector<std::string>& stmts, const std::string& name, size_t max_stmts);

    std::vector<std::string> getSymCtorStmts();
    std::vector<std::string> getSymDtorStmts();

    static size_t stmtCost(const std::string& stmt) {
        if (stmt.empty()) return 0;
        if (VString::startsWith(stmt, "/")) return 0;
        return static_cast<size_t>(AstNode::INSTR_COUNT_SYM);
    }

    static void nameCheck(AstNode* nodep) {
        // Prevent GCC compile time error; name check all things that reach C++ code
        if (nodep->name().empty()) return;
        const AstCFunc* const cfuncp = VN_CAST(nodep, CFunc);
        if (!cfuncp || (!cfuncp->isConstructor() && !cfuncp->isDestructor())) {
            const std::string rsvd = V3LanguageWords::isKeyword(nodep->name());
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

    static std::string scopeSymString(const std::string& scpname) {
        std::string out = scpname;
        std::string::size_type pos;
        while ((pos = out.find("__PVT__")) != std::string::npos) out.replace(pos, 7, "");
        if (VString::startsWith(out, "TOP__DOT__")) out.replace(0, 10, "");
        if (VString::startsWith(out, "TOP.")) out.replace(0, 4, "");
        while ((pos = out.find('.')) != std::string::npos) out.replace(pos, 1, "__");
        while ((pos = out.find("__DOT__")) != std::string::npos) out.replace(pos, 7, "__");
        return out;
    }

    static string scopeDecodeIdentifier(const std::string& scpname) {
        std::string::size_type pos = std::string::npos;

        // Remove hierarchy
        size_t i = 0;
        // always makes progress
        while (i < scpname.length()) {
            if (scpname[i] == '\\') {
                while (i < scpname.length() && scpname[i] != ' ') ++i;
                ++i;  // Proc ' ', it should always be there. Then grab '.' on next cycle
            } else {
                while (i < scpname.length() && scpname[i] != '.') ++i;
                if (i < scpname.length()) pos = i++;
            }
        }

        return pos != std::string::npos ? scpname.substr(pos + 1) : scpname;
    }

    /// (scp, m_vpiScopeCandidates, m_scopeNames) -> m_scopeNames
    /// Look for parent scopes of scp in m_vpiScopeCandidates (separated by __DOT__ or ".")
    /// Then add/update entry in m_scopeNames if not already there
    void varHierarchyScopes(std::string scp) {

        std::string::size_type prd_pos = scp.rfind('.');
        std::string::size_type dot_pos = scp.rfind("__DOT__");

        while (!scp.empty()) {
            const auto scpit = m_vpiScopeCandidates.find(scopeSymString(scp));
            if ((scpit != m_vpiScopeCandidates.end())
                && (m_scopeNames.find(scp) == m_scopeNames.end())) {
                // If not in m_scopeNames, add it, otherwise just update m_type
                const auto pair = m_scopeNames.emplace(scpit->second.m_symName, scpit->second);
                if (!pair.second) pair.first->second.m_type = scpit->second.m_type;
            }

            // resize and advance pointers
            if ((prd_pos < dot_pos || prd_pos == string::npos) && dot_pos != string::npos) {
                scp.resize(dot_pos);
                dot_pos = scp.rfind("__DOT__");
            } else {
                if (prd_pos == string::npos) break;
                scp.resize(prd_pos);
                prd_pos = scp.rfind('.');
            }
        }
    }

    void varsExpand() {
        // We didn't have all m_scopes loaded when we encountered variables, so expand them now
        // It would be less code if each module inserted its own variables.
        // Someday.
        for (const ScopeModPair& smPair : m_scopes) {
            const AstScope* const scopep = smPair.first;
            const AstNodeModule* const smodp = smPair.second;
            for (const ModVarPair& mvPair : m_modVars) {
                const AstNodeModule* const modp = mvPair.first;
                const AstVar* const varp = mvPair.second;
                if (modp != smodp) continue;

                // Need to split the module + var name into the
                // original-ish full scope and variable name under that scope.
                // The module instance name is included later, when we
                // know the scopes this module is under
                std::string whole = scopep->name() + "__DOT__" + varp->name();
                std::string scpName;
                std::string varBase;
                if (VString::startsWith(whole, "__DOT__TOP")) whole.replace(0, 10, "");
                const std::string::size_type dpos = whole.rfind("__DOT__");
                if (dpos != std::string::npos) {
                    scpName = whole.substr(0, dpos);
                    varBase = whole.substr(dpos + std::strlen("__DOT__"));
                } else {
                    varBase = whole;
                }
                // UINFO(9, "For " << scopep->name() << " - " << varp->name() << "  Scp "
                // << scpName << "Var " << varBase);
                const std::string varBasePretty = AstNode::vpiName(VName::dehash(varBase));
                const std::string scpPretty = AstNode::prettyName(VName::dehash(scpName));
                const std::string scpSym = scopeSymString(VName::dehash(scpName));
                // UINFO(9, " scnameins sp " << scpName << " sp " << scpPretty << " ss "
                // << scpSym);
                if (v3Global.opt.vpi()) varHierarchyScopes(scpName);

                m_scopeNames.emplace(  //
                    std::piecewise_construct,  //
                    std::forward_as_tuple(scpSym),  //
                    std::forward_as_tuple(varp, scpSym, scpPretty, "<null>", 0, "SCOPE_OTHER"));

                m_scopeVars.emplace(  //
                    std::piecewise_construct,  //
                    std::forward_as_tuple(scpSym + " " + varp->name()),  //
                    std::forward_as_tuple(scpSym, varBasePretty, varp, modp, scopep));
            }
        }
    }

    void buildVpiHierarchy() {
        for (const auto& itpair : m_scopeNames) {
            const std::string symName = itpair.second.m_symName;
            std::string above = symName;
            if (VString::startsWith(above, "TOP.")) above.replace(0, 4, "");

            while (!above.empty()) {
                const std::string::size_type pos = above.rfind("__");
                if (pos == std::string::npos) break;
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
    void visit(AstNetlist* nodep) override {
        // Collect list of scopes
        iterateChildrenConst(nodep);
        varsExpand();

        if (v3Global.opt.vpi()) buildVpiHierarchy();

        if (v3Global.dpi()) {
            // add dpi scopes to m_scopeNames if not already there
            for (const auto& scp : m_dpiScopeNames) m_scopeNames.emplace(scp.first, scp.second);
        }

        // Sort by names, so line/process order matters less
        std::stable_sort(m_scopes.begin(), m_scopes.end(),
                         [](const ScopeModPair& a, const ScopeModPair& b) {
                             return a.first->name() < b.first->name();
                         });
        std::stable_sort(m_dpis.begin(), m_dpis.end(),  //
                         [](const AstCFunc* ap, const AstCFunc* bp) {
                             if (ap->dpiImportPrototype() != bp->dpiImportPrototype()) {
                                 return bp->dpiImportPrototype();
                             }
                             return ap->name() < bp->name();
                         });

        // Output
        if (!m_dpiHdrOnly) {
            // Must emit implementation first to determine number of splits
            emitSymImp(nodep);
            emitSymHdr();
        }
        if (v3Global.dpi()) {
            emitDpiHdr();
            if (!m_dpiHdrOnly) emitDpiImp();
        }
    }
    void visit(AstConstPool* nodep) override {}  // Ignore
    void visit(AstNodeModule* nodep) override {
        nameCheck(nodep);
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstCellInlineScope* nodep) override {
        if (!v3Global.opt.vpi()) return;

        const std::string type = (nodep->origModName() == "__BEGIN__") ? "SCOPE_OTHER"  //
                                                                       : "SCOPE_MODULE";
        const std::string name = nodep->scopep()->shortName() + "__DOT__" + nodep->name();
        const int timeunit = m_modp->timeunit().powerOfTen();
        m_vpiScopeCandidates.emplace(  //
            std::piecewise_construct,  //
            std::forward_as_tuple(scopeSymString(name)),  //
            std::forward_as_tuple(nodep, scopeSymString(name), AstNode::vpiName(name),
                                  type == "SCOPE_MODULE" ? nodep->origModName() : "<null>",
                                  timeunit, type));
    }
    void visit(AstScope* nodep) override {
        if (VN_IS(m_modp, Class)) return;  // The ClassPackage is what is visible
        nameCheck(nodep);

        m_scopes.emplace_back(nodep, m_modp);

        if (v3Global.opt.vpi() && !nodep->isTop()) {
            const std::string type = VN_IS(nodep->modp(), Package) ? "SCOPE_PACKAGE"  //
                                                                   : "SCOPE_MODULE";
            const int timeunit = m_modp->timeunit().powerOfTen();
            m_vpiScopeCandidates.emplace(  //
                std::piecewise_construct,  //
                std::forward_as_tuple(scopeSymString(nodep->name())),  //
                std::forward_as_tuple(nodep, scopeSymString(nodep->name()),
                                      AstNode::vpiName(nodep->shortName()),
                                      nodep->modp()->origName(), timeunit, type));
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstScopeName* nodep) override {
        const std::string name = nodep->scopeSymName();
        // UINFO(9, "scnameins sp " << nodep->name() << " sp " << nodep->scopePrettySymName()
        // << " ss" << name);
        const int timeunit = m_modp ? m_modp->timeunit().powerOfTen() : 0;
        m_dpiScopeNames.emplace(  //
            std::piecewise_construct,  //
            std::forward_as_tuple(name),  //
            std::forward_as_tuple(nodep, name, nodep->scopePrettySymName(), "<null>", timeunit,
                                  "SCOPE_OTHER"));

        if (nodep->dpiExport()) {
            UASSERT_OBJ(m_cfuncp, nodep, "ScopeName not under DPI function");
            m_scopeFuncs.emplace(  //
                std::piecewise_construct,  //
                std::forward_as_tuple(name + " " + m_cfuncp->name()),  //
                std::forward_as_tuple(nodep, m_cfuncp, m_modp));
        } else {
            // Note emplace does not construct when duplicate key
            m_dpiScopeNames.emplace(  //
                std::piecewise_construct,  //
                std::forward_as_tuple(nodep->scopeDpiName()),  //
                std::forward_as_tuple(nodep, nodep->scopeDpiName(), nodep->scopePrettyDpiName(),
                                      "<null>", timeunit, "SCOPE_OTHER"));
        }
    }
    void visit(AstVar* nodep) override {
        nameCheck(nodep);
        iterateChildrenConst(nodep);
        // Record if public, ignoring locals
        if ((nodep->isSigUserRdPublic() || nodep->isSigUserRWPublic()) && !m_cfuncp) {
            m_modVars.emplace_back(m_modp, nodep);
        }
    }
    void visit(AstNodeCoverDecl* nodep) override {
        // Assign numbers to all bins, so we know how big of an array to use
        if (!nodep->dataDeclNullp()) {  // else duplicate we don't need code for
            nodep->binNum(m_coverBins);
            m_coverBins += nodep->size();
        }
    }
    void visit(AstCFunc* nodep) override {
        nameCheck(nodep);
        if (nodep->dpiImportPrototype() || nodep->dpiExportDispatcher()) m_dpis.push_back(nodep);
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildrenConst(nodep);
    }

    //---------------------------------------
    void visit(AstConst*) override {}
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit EmitCSyms(AstNetlist* nodep, bool dpiHdrOnly)
        : m_dpiHdrOnly{dpiHdrOnly} {
        iterateConst(nodep);
    }
};

void EmitCSyms::emitSymHdr() {
    UINFO(6, __FUNCTION__ << ": ");
    openNewOutputHeaderFile(symClassName(), "Symbol table internal header");
    puts("//\n");
    puts("// Internal details; most calling programs do not need this header,\n");
    puts("// unless using verilator public meta comments.\n");

    ofp()->putsGuard();

    puts("\n");
    ofp()->putsIntTopInclude();
    puts("#include \"verilated.h\"\n");
    if (v3Global.needTraceDumper()) {
        for (const string& base : v3Global.opt.traceSourceLangs())
            puts("#include \"" + base + ".h\"\n");
    }
    if (v3Global.opt.usesProfiler()) puts("#include \"verilated_profiler.h\"\n");

    puts("\n// INCLUDE MODEL CLASS\n");
    puts("\n#include \"" + topClassName() + ".h\"\n");

    puts("\n// INCLUDE MODULE CLASSES\n");
    for (AstNodeModule *nodep = v3Global.rootp()->modulesp(), *nextp; nodep; nodep = nextp) {
        nextp = VN_AS(nodep->nextp(), NodeModule);
        if (VN_IS(nodep, Class)) continue;  // Class included earlier
        putns(nodep, "#include \"" + EmitCUtil::prefixNameProtect(nodep) + ".h\"\n");
    }

    if (v3Global.dpi()) {
        puts("\n// DPI TYPES for DPI Export callbacks (Internal use)\n");
        std::set<std::string> types;  // Remove duplicates and sort
        for (const auto& itpair : m_scopeFuncs) {
            const AstCFunc* const funcp = itpair.second.m_cfuncp;
            if (!funcp->dpiExportImpl()) continue;
            const std::string cbtype
                = protect(v3Global.opt.prefix() + "__Vcb_" + funcp->cname() + "_t");
            const std::string functype = funcp->rtnTypeVoid() + " (*) (" + cFuncArgs(funcp) + ")";
            types.emplace("using " + cbtype + " = " + functype + ";\n");
        }
        for (const std::string& type : types) puts(type);
    }

    puts("\n// SYMS CLASS (contains all model state)\n");
    puts("class alignas(VL_CACHE_LINE_BYTES) " + symClassName()
         + " final : public VerilatedSyms {\n");
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
    if (v3Global.hasEvents()) {
        if (v3Global.assignsEvents()) {
            puts("std::vector<VlAssignableEvent> __Vm_triggeredEvents;\n");
        } else {
            puts("std::vector<VlEvent*> __Vm_triggeredEvents;\n");
        }
    }
    if (v3Global.hasClasses()) puts("VlDeleter __Vm_deleter;\n");
    puts("bool __Vm_didInit = false;\n");

    if (v3Global.opt.mtasks()) {
        puts("\n// MULTI-THREADING\n");
        puts("VlThreadPool* __Vm_threadPoolp;\n");
        puts("bool __Vm_even_cycle__ico = false;\n");
        puts("bool __Vm_even_cycle__act = false;\n");
        puts("bool __Vm_even_cycle__nba = false;\n");
    }

    if (v3Global.opt.profExec()) {
        puts("\n// EXECUTION PROFILING\n");
        puts("VlExecutionProfiler* const __Vm_executionProfilerp;\n");
    }

    if (v3Global.opt.profPgo()) {
        puts("\n// PGO PROFILING\n");
        puts("VlPgoProfiler<" + std::to_string(ExecMTask::numUsedIds()) + "> _vm_pgoProfiler;\n");
    }

    puts("\n// MODULE INSTANCE STATE\n");
    for (const ScopeModPair& itpair : m_scopes) {
        const AstScope* const scopep = itpair.first;
        const AstNodeModule* const modp = itpair.second;
        if (VN_IS(modp, Class)) continue;
        const std::string name = EmitCUtil::prefixNameProtect(modp);
        ofp()->printf("%-30s ", name.c_str());
        putns(scopep, VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + ";\n");
    }

    if (m_coverBins) {
        puts("\n// COVERAGE\n");
        puts(v3Global.opt.threads() > 1 ? "std::atomic<uint32_t>" : "uint32_t");
        puts(" __Vcoverage[");
        puts(std::to_string(m_coverBins));
        puts("];\n");
    }

    if (!m_scopeNames.empty()) {  // Scope names
        puts("\n// SCOPE NAMES\n");
        for (const auto& itpair : m_scopeNames) {
            const ScopeData& sd = itpair.second;
            putns(sd.m_nodep, "VerilatedScope* " + protect("__Vscopep_" + sd.m_symName) + ";\n");
        }
    }

    if (v3Global.opt.vpi()) {
        puts("\n// SCOPE HIERARCHY\n");
        puts("VerilatedHierarchy __Vhier;\n");
    }

    puts("\n// CONSTRUCTORS\n");
    puts(symClassName() + "(VerilatedContext* contextp, const char* namep, " + topClassName()
         + "* modelp);\n");
    puts("~" + symClassName() + "();\n");

    for (const std::string& funcName : m_splitFuncNames) { puts("void " + funcName + "();\n"); }

    puts("\n// METHODS\n");
    puts("const char* name() const { return TOP.vlNamep; }\n");

    if (v3Global.hasEvents()) {
        if (v3Global.assignsEvents()) {
            puts("void fireEvent(VlAssignableEvent& event) {\n");
        } else {
            puts("void fireEvent(VlEvent& event) {\n");
        }
        puts("if (VL_LIKELY(!event.isTriggered())) {\n");
        if (v3Global.assignsEvents()) {
            puts("__Vm_triggeredEvents.push_back(event);\n");
        } else {
            puts("__Vm_triggeredEvents.push_back(&event);\n");
        }
        puts("}\n");
        puts("event.fire();\n");
        puts("}\n");
        puts("void clearTriggeredEvents() {\n");
        if (v3Global.assignsEvents()) {
            puts("for (auto& event : __Vm_triggeredEvents) event.clearTriggered();\n");
        } else {
            puts("for (const auto eventp : __Vm_triggeredEvents) eventp->clearTriggered();\n");
        }
        puts("__Vm_triggeredEvents.clear();\n");
        puts("}\n");
    }

    if (v3Global.needTraceDumper()) {
        if (!optSystemC()) puts("void _traceDump();\n");
        puts("void _traceDumpOpen();\n");
        puts("void _traceDumpClose();\n");
    }

    if (v3Global.opt.savable()) {
        puts("void " + protect("__Vserialize") + "(VerilatedSerialize& os);\n");
        puts("void " + protect("__Vdeserialize") + "(VerilatedDeserialize& os);\n");
    }
    puts("};\n");

    ofp()->putsEndGuard();
    closeOutputFile();
}

void EmitCSyms::emitSymImpPreamble() {
    puts("\n");

    // Includes
    puts("#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
    puts("\n");
    // Declarations for DPI Export implementation functions
    bool needsNewLine = false;
    for (const auto& itpair : m_scopeFuncs) {
        const AstCFunc* const funcp = itpair.second.m_cfuncp;
        if (!funcp->dpiExportImpl()) continue;
        emitCFuncDecl(funcp, itpair.second.m_modp);
        needsNewLine = true;
    }
    if (needsNewLine) puts("\n");
}

void EmitCSyms::emitScopeHier(std::vector<std::string>& stmts, bool destroy) {
    if (!v3Global.opt.vpi()) return;

    if (destroy) {
        stmts.emplace_back("// Tear down scope hierarchy");
    } else {
        stmts.emplace_back("// Set up scope hierarchy");
    }

    const std::string method = destroy ? "remove" : "add";
    for (const auto& itpair : m_scopeNames) {
        if (itpair.first == "TOP") continue;
        const ScopeData& sd = itpair.second;
        const std::string& name = sd.m_prettyName;
        const std::string& scopeType = sd.m_type;
        if (name.find('.') != string::npos) continue;
        if (scopeType != "SCOPE_MODULE" && scopeType != "SCOPE_PACKAGE") continue;
        const std::string id = protect("__Vscopep_" + sd.m_symName);
        stmts.emplace_back("__Vhier." + method + "(0, " + id + ");");
    }
    for (const auto& itpair : m_vpiScopeHierarchy) {
        const std::string fromName = scopeSymString(itpair.first);
        const std::string fromId = protect("__Vscopep_" + m_scopeNames.at(fromName).m_symName);
        for (const std::string& name : itpair.second) {
            const std::string toName = scopeSymString(name);
            const std::string toId = protect("__Vscopep_" + m_scopeNames.at(toName).m_symName);
            stmts.emplace_back("__Vhier." + method + "(" + fromId + ", " + toId + ");");
        }
    }

    if (destroy) {
        stmts.emplace_back("// Clear keys from hierarchy map after values have been removed");
        stmts.emplace_back("__Vhier.clear();");
    }
}

std::vector<std::string> EmitCSyms::getSymCtorStmts() {
    std::vector<std::string> stmts;

    const auto add = [&stmts](const std::string& stmt) { stmts.emplace_back(stmt); };

    {
        uint64_t stackSize = V3StackCount::count(v3Global.rootp());
        if (v3Global.opt.debugStackCheck()) stackSize += 1024 * 1024 * 1024;
        V3Stats::addStat("Size prediction, Stack (bytes)", stackSize);
        // TODO: 'm_statVarScopeBytes' is always 0, AstVarScope doesn't reach here (V3Descope)
        V3Stats::addStat("Size prediction, Heap, from Var Scopes (bytes)", m_statVarScopeBytes);
        V3Stats::addStat(V3Stats::STAT_MODEL_SIZE, stackSize + m_statVarScopeBytes);

        add("// Check resources");
        add("Verilated::stackCheck(" + std::to_string(stackSize) + ");");
    }

    add("// Setup sub module instances");
    for (const ScopeModPair& itpair : m_scopes) {
        const AstScope* const scopep = itpair.first;
        const AstNodeModule* const modp = itpair.second;
        if (modp->isTop()) continue;
        const std::string name = V3OutFormatter::quoteNameControls(
            VIdProtect::protectWordsIf(scopep->prettyName(), scopep->protect()));
        add(protect(scopep->nameDotless()) + ".ctor(this, \"" + name + "\");");
    }

    if (v3Global.opt.profPgo()) {
        add("// Configure profiling for PGO\n");
        if (!v3Global.opt.hierChild()) {
            add("_vm_pgoProfiler.writeHeader(_vm_contextp__->profVltFilename());");
        }
        if (v3Global.opt.mtasks()) {
            v3Global.rootp()->topModulep()->foreach([&](const AstExecGraph* execGraphp) {
                for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                    const ExecMTask& mt = static_cast<const ExecMTask&>(vtx);
                    add("_vm_pgoProfiler.addCounter(" + std::to_string(mt.id()) + ", \""
                        + mt.hashName() + "\");");
                }
            });
        }
    }

    add("// Configure time unit / time precision");
    if (!v3Global.rootp()->timeunit().isNone()) {
        const std::string unit = std::to_string(v3Global.rootp()->timeunit().powerOfTen());
        add("_vm_contextp__->timeunit(" + unit + ");");
    }
    if (!v3Global.rootp()->timeprecision().isNone()) {
        const std::string prec = std::to_string(v3Global.rootp()->timeprecision().powerOfTen());
        add("_vm_contextp__->timeprecision(" + prec + ");");
    }

    add("// Setup each module's pointers to their submodules");
    for (const auto& i : m_scopes) {
        const AstScope* const scopep = i.first;
        const AstNodeModule* const modp = i.second;
        const AstScope* const abovep = scopep->aboveScopep();
        if (!abovep) continue;

        const std::string protName = VIdProtect::protectWordsIf(scopep->name(), scopep->protect());
        std::string stmt;
        if (VN_IS(modp, ClassPackage)) {
            // ClassPackage modules seem to be a bit out of place, so hard code...
            stmt += "TOP";
        } else {
            stmt += VIdProtect::protectIf(abovep->nameDotless(), abovep->protect());
        }
        stmt += ".";
        stmt += protName.substr(protName.rfind('.') + 1);
        stmt += " = &";
        stmt += VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + ";";
        add(stmt);
    }

    add("// Setup each module's pointer back to symbol table (for public functions)");
    for (const ScopeModPair& i : m_scopes) {
        const AstScope* const scopep = i.first;
        AstNodeModule* const modp = i.second;
        // first is used by AstCoverDecl's call to __vlCoverInsert
        const bool first = !modp->user1();
        modp->user1(true);
        add(VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + "."
            + protect("__Vconfigure") + "(" + (first ? "true" : "false") + ");");
    }

    add("// Setup scopes");
    for (const auto& itpair : m_scopeNames) {
        const ScopeData& sd = itpair.second;
        std::string stmt;
        stmt += protect("__Vscopep_" + sd.m_symName) + " = new VerilatedScope{this, \"";
        stmt += V3OutFormatter::quoteNameControls(
            VIdProtect::protectWordsIf(sd.m_prettyName, true));
        stmt += "\", \"";
        stmt += V3OutFormatter::quoteNameControls(protect(scopeDecodeIdentifier(sd.m_prettyName)));
        stmt += "\", \"";
        stmt += V3OutFormatter::quoteNameControls(sd.m_defName);
        stmt += "\", ";
        stmt += std::to_string(sd.m_timeunit);
        stmt += ", VerilatedScope::" + sd.m_type + "};";
        add(stmt);
    }

    emitScopeHier(stmts, false);

    if (v3Global.dpi()) {
        for (const std::string vfinal : {"0", "1"}) {
            add("// Setup export functions - final: " + vfinal);
            for (const auto& itpair : m_scopeFuncs) {
                const ScopeFuncData& sfd = itpair.second;
                const AstScopeName* const scopep = sfd.m_scopep;
                const AstCFunc* const funcp = sfd.m_cfuncp;
                const AstNodeModule* const modp = sfd.m_modp;
                if (!funcp->dpiExportImpl()) continue;

                std::string stmt;
                stmt += protect("__Vscopep_" + scopep->scopeSymName()) + "->exportInsert(";
                stmt += vfinal + ", \"";
                // Not protected - user asked for import/export
                stmt += V3OutFormatter::quoteNameControls(funcp->cname());
                stmt += "\", (void*)(&";
                stmt += EmitCUtil::prefixNameProtect(modp);
                stmt += "__";
                stmt += funcp->nameProtect();
                stmt += "));";
                add(stmt);
            }
        }
    }

    // It would be less code if each module inserted its own variables. Someday.
    if (!m_scopeVars.empty()) {
        add("// Setup public variables");
        for (const auto& itpair : m_scopeVars) {
            const ScopeVarData& svd = itpair.second;
            const AstScope* const scopep = svd.m_scopep;
            const AstVar* const varp = svd.m_varp;
            int pdim = 0;
            int udim = 0;
            std::string bounds;
            if (const AstBasicDType* const basicp = varp->basicp()) {
                // Range is always first, it's not in "C" order
                for (AstNodeDType* dtypep = varp->dtypep(); dtypep;) {
                    // Skip AstRefDType/AstTypedef, or return same node
                    dtypep = dtypep->skipRefp();
                    if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                        bounds += " ,";
                        bounds += std::to_string(adtypep->left());
                        bounds += ",";
                        bounds += std::to_string(adtypep->right());
                        if (VN_IS(dtypep, PackArrayDType))
                            pdim++;
                        else
                            udim++;
                        dtypep = adtypep->subDTypep();
                    } else {
                        if (basicp->isRanged()) {
                            bounds += " ,";
                            bounds += std::to_string(basicp->left());
                            bounds += ",";
                            bounds += std::to_string(basicp->right());
                            pdim++;
                        }
                        break;  // AstBasicDType - nothing below, 1
                    }
                }
            }

            std::string stmt;
            stmt += protect("__Vscopep_" + svd.m_scopeName) + "->varInsert(\"";
            stmt += V3OutFormatter::quoteNameControls(protect(svd.m_varBasePretty)) + '"';

            const std::string varName
                = VIdProtect::protectIf(scopep->nameDotless(), scopep->protect()) + "."
                  + protect(varp->name());

            if (!varp->isParam()) {
                stmt += ", &(";
                stmt += varName;
                stmt += "), false, ";
            } else if (varp->vlEnumType() == "VLVT_STRING"
                       && !VN_IS(varp->subDTypep(), UnpackArrayDType)) {
                stmt += ", const_cast<void*>(static_cast<const void*>(";
                stmt += varName;
                stmt += ".c_str())), true, ";
            } else {
                stmt += ", const_cast<void*>(static_cast<const void*>(&(";
                stmt += varName;
                stmt += "))), true, ";
            }

            stmt += varp->vlEnumType();  // VLVT_UINT32 etc
            stmt += ", ";
            stmt += varp->vlEnumDir();  // VLVD_IN etc
            if (varp->dtypep()->skipRefp()->isSigned()) stmt += "|VLVF_SIGNED";
            stmt += ", ";
            stmt += std::to_string(udim);
            stmt += ", ";
            stmt += std::to_string(pdim);
            stmt += bounds;
            stmt += ");";
            add(stmt);
        }
    }

    return stmts;
}

std::vector<std::string> EmitCSyms::getSymDtorStmts() {
    std::vector<std::string> stmts;

    const auto add = [&stmts](const std::string& stmt) { stmts.emplace_back(stmt); };

    emitScopeHier(stmts, true);
    if (v3Global.needTraceDumper()) add("if (__Vm_dumping) _traceDumpClose();");
    if (v3Global.opt.profPgo()) {
        add("_vm_pgoProfiler.write(\"" + topClassName()
            + "\", _vm_contextp__->profVltFilename());");
    }
    add("// Tear down scopes");
    for (const auto& itpair : m_scopeNames) {
        const ScopeData& sd = itpair.second;
        const std::string id = protect("__Vscopep_" + sd.m_symName);
        add("VL_DO_CLEAR(delete " + id + ", " + id + " = nullptr);");
    }

    add("// Tear down sub module instances");
    for (const ScopeModPair& itpair : vlstd::reverse_view(m_scopes)) {
        const AstScope* const scopep = itpair.first;
        const AstNodeModule* const modp = itpair.second;
        if (modp->isTop()) continue;
        add(protect(scopep->nameDotless()) + ".dtor();");
    }
    return stmts;
}

void EmitCSyms::emitSplit(std::vector<std::string>& stmts, const std::string& name,
                          size_t maxCost) {
    size_t nSubFunctions = 0;
    // Reduce into a balanced tree of sub-function calls until we end up with a single statement
    while (stmts.size() > 1) {
        size_t nSplits = 0;
        size_t nStmts = stmts.size();
        for (size_t splitStart = 0, splitEnd = 0; splitStart < nStmts; splitStart = splitEnd) {
            // Gather up at at most 'maxCost' worth of statements in this split,
            // but always at least 2 (if less than 2, the reduction makes no
            // progress and the loop will not terminate).
            size_t cost = 0;
            while (((cost < maxCost) || (splitEnd - splitStart < 2)) && splitEnd < nStmts) {
                cost += stmtCost(stmts[splitEnd++]);
            }
            UASSERT(splitStart < splitEnd, "Empty split");

            // Create new sub-function and emit current range of statementss
            const std::string nStr = std::to_string(nSubFunctions++);
            // Name of sub-function we are emitting now
            const std::string funcName = symClassName() + "__" + name + "__" + nStr;
            m_splitFuncNames.emplace_back(funcName);
            // Open split file
            openNewOutputSourceFile(funcName, true, true, "Symbol table implementation internals");
            // Emit header
            emitSymImpPreamble();
            // Open sub-function definition in the split file
            puts("void " + symClassName() + "::" + funcName + "() {\n");

            // Emit statements
            for (size_t j = splitStart; j < splitEnd; ++j) {
                ofp()->putsNoTracking("    ");
                ofp()->putsNoTracking(stmts[j]);
                ofp()->putsNoTracking("\n");
            }

            // Close sub-function
            puts("}\n");
            // Close split file
            closeOutputFile();

            // Replace statements with a call to the sub-function
            stmts[nSplits++] = funcName + "();";
        }
        // The statements at the front are now the calls to the sub-functions, drop the rest
        stmts.resize(nSplits);
    }
}

void EmitCSyms::emitSymImp(const AstNetlist* netlistp) {
    UINFO(6, __FUNCTION__ << ": ");

    // Get the body of the constructor and destructor
    std::vector<std::string> ctorStmts = getSymCtorStmts();
    std::vector<std::string> dtorStmts = getSymDtorStmts();

    // Check if needs splitting and if so split into sub-functions
    if (const size_t maxCost = static_cast<size_t>(v3Global.opt.outputSplitCFuncs())) {
        size_t totalCost = 200;  // Starting from 200 to consider all other contents in main file
        if (totalCost <= maxCost) {
            for (const std::string& stmt : ctorStmts) {
                totalCost += stmtCost(stmt);
                if (totalCost > maxCost) break;
            }
        }
        if (totalCost <= maxCost) {
            for (const std::string& stmt : dtorStmts) {
                totalCost += stmtCost(stmt);
                if (totalCost > maxCost) break;
            }
        }
        // Split them if needed
        if (totalCost > maxCost) {
            v3Global.useParallelBuild(true);  // Splitting files, so using parallel build.
            emitSplit(ctorStmts, "ctor", maxCost);
            emitSplit(dtorStmts, "dtor", maxCost);
        }
    }

    openNewOutputSourceFile(symClassName(), true, true, "Symbol table implementation internals");
    emitSymImpPreamble();

    // Constructor
    const std::string ctorArgs
        = "VerilatedContext* contextp, const char* namep, " + topClassName() + "* modelp";
    puts(symClassName() + "::" + symClassName() + "(" + ctorArgs + ")\n");
    puts("    : VerilatedSyms{contextp}\n");
    puts("    // Setup internal state of the Syms class\n");
    puts("    , __Vm_modelp{modelp}\n");
    if (v3Global.opt.mtasks()) {
        puts("    , __Vm_threadPoolp{static_cast<VlThreadPool*>(contextp->threadPoolp())}\n");
    }
    if (v3Global.opt.profExec()) {
        puts("    , __Vm_executionProfilerp{static_cast<VlExecutionProfiler*>(contextp->"
             "enableExecutionProfiler(&VlExecutionProfiler::construct))}\n");
    }
    if (v3Global.opt.profPgo() && !v3Global.opt.libCreate().empty()) {
        puts("    , _vm_pgoProfiler{" + std::to_string(v3Global.currentHierBlockCost()) + "}\n");
    }
    {
        const AstScope* const scopep = netlistp->topScopep()->scopep();
        puts("    // Setup top module instance\n");
        puts("    , " + protect(scopep->nameDotless()) + "{this, namep}\n");
    }
    puts("{\n");
    for (const std::string& stmt : ctorStmts) {
        ofp()->putsNoTracking("    ");
        ofp()->putsNoTracking(stmt);
        ofp()->putsNoTracking("\n");
    }
    puts("}\n");

    // Destructor
    puts("\n" + symClassName() + "::~" + symClassName() + "() {\n");
    for (const std::string& stmt : dtorStmts) {
        ofp()->putsNoTracking("    ");
        ofp()->putsNoTracking(stmt);
        ofp()->putsNoTracking("\n");
    }
    puts("}\n");

    // Methods
    if (v3Global.needTraceDumper()) {
        if (!optSystemC()) {
            puts("\nvoid " + symClassName() + "::_traceDump() {\n");
            puts("const VerilatedLockGuard lock{__Vm_dumperMutex};\n");
            // Caller checked for __Vm_dumperp non-nullptr
            puts("__Vm_dumperp->dump(VL_TIME_Q());\n");
            puts("}\n");
        }

        puts("\nvoid " + symClassName() + "::_traceDumpOpen() {\n");
        puts("const VerilatedLockGuard lock{__Vm_dumperMutex};\n");
        puts("if (VL_UNLIKELY(!__Vm_dumperp)) {\n");
        puts("__Vm_dumperp = new " + v3Global.opt.traceClassLang() + "();\n");
        puts("__Vm_modelp->trace(__Vm_dumperp, 0, 0);\n");
        puts("const std::string dumpfile = _vm_contextp__->dumpfileCheck();\n");
        puts("__Vm_dumperp->open(dumpfile.c_str());\n");
        puts("__Vm_dumping = true;\n");
        puts("}\n");
        puts("}\n");

        puts("\nvoid " + symClassName() + "::_traceDumpClose() {\n");
        puts("const VerilatedLockGuard lock{__Vm_dumperMutex};\n");
        puts("__Vm_dumping = false;\n");
        puts("VL_DO_CLEAR(delete __Vm_dumperp, __Vm_dumperp = nullptr);\n");
        puts("}\n");
    }

    if (v3Global.opt.savable()) {
        for (const bool& de : {false, true}) {
            const std::string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
            const std::string funcname = protect(de ? "__Vdeserialize" : "__Vserialize");
            const std::string op = de ? ">>" : "<<";
            puts("\nvoid " + symClassName() + "::" + funcname + "(" + classname + "& os) {\n");
            puts("// Internal state\n");
            if (v3Global.opt.trace()) puts("os" + op + "__Vm_activity;\n");
            puts("os " + op + " __Vm_didInit;\n");
            puts("// Module instance state\n");
            for (const ScopeModPair& itpair : m_scopes) {
                const AstScope* const scopep = itpair.first;
                const std::string scopeName
                    = VIdProtect::protectIf(scopep->nameDotless(), scopep->protect());
                puts(scopeName + "." + funcname + "(os);\n");
            }
            puts("}\n");
        }
    }

    closeOutputFile();
}

//######################################################################

void EmitCSyms::emitDpiHdr() {
    UINFO(6, __FUNCTION__ << ": ");

    openNewOutputHeaderFile(topClassName() + "__Dpi",
                            "Prototypes for DPI import and export functions.");
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
    for (const AstCFunc* const nodep : m_dpis) {
        if (!nodep->dpiExportDispatcher() && !nodep->dpiImportPrototype()) continue;

        const std::string sourceLoc = VIdProtect::ifNoProtect(" at " + nodep->fileline()->ascii());
        if (nodep->dpiExportDispatcher()) {
            if (!firstExp++) puts("\n// DPI EXPORTS\n");
            putsDecoration(nodep, "// DPI export" + sourceLoc + "\n");
        } else {
            if (!firstImp++) puts("\n// DPI IMPORTS\n");
            putsDecoration(nodep, "// DPI import" + sourceLoc + "\n");
        }
        putns(nodep, "extern " + nodep->rtnTypeVoid() + " " + nodep->nameProtect() + "("
                         + cFuncArgs(nodep) + ");\n");
    }

    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("}\n");
    puts("#endif\n");

    ofp()->putsEndGuard();

    closeOutputFile();
}

//######################################################################

void EmitCSyms::emitDpiImp() {
    UINFO(6, __FUNCTION__ << ": ");
    openNewOutputSourceFile(topClassName() + "__Dpi", false, true,
                            "Implementation of DPI export functions");
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

    for (const AstCFunc* const nodep : m_dpis) {
        if (!nodep->dpiExportDispatcher()) continue;

        const std::string name = nodep->name();
        const std::string sourceLoc = VIdProtect::ifNoProtect(" at " + nodep->fileline()->ascii());

        // Prevent multi-definition if used by multiple models
        puts("#ifndef VL_DPIDECL_" + name + "_\n");
        puts("#define VL_DPIDECL_" + name + "_\n");
        putns(nodep, nodep->rtnTypeVoid() + " " + name + "(" + cFuncArgs(nodep) + ") {\n");
        puts("// DPI export" + sourceLoc + "\n");
        putns(nodep, "return " + topClassName() + "::" + name + "(");
        std::string comma;
        for (const AstNode* stmtp = nodep->argsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn()) {
                    puts(comma);
                    comma = ", ";
                    putns(portp, portp->name());
                }
            }
        }
        puts(");\n");
        puts("}\n");
        puts("#endif\n");
        puts("\n");
    }
    closeOutputFile();
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcSyms(bool dpiHdrOnly) {
    UINFO(2, __FUNCTION__ << ":");
    EmitCSyms{v3Global.rootp(), dpiHdrOnly};
}
