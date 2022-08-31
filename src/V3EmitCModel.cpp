// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for model entry point class
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
#include "V3EmitCFunc.h"
#include "V3Global.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <functional>
#include <vector>

class EmitCModel final : public EmitCFunc {
    // TYPES
    using CFuncVector = std::vector<const AstCFunc*>;

    // MEMBERS
    V3UniqueNames m_uniqueNames;  // For generating unique file names

    // METHODS
    VL_DEBUG_FUNC;

    CFuncVector findFuncps(std::function<bool(const AstCFunc*)> cb) {
        CFuncVector funcps;
        for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCFunc* const funcp = VN_CAST(nodep, CFunc)) {
                if (cb(funcp)) funcps.push_back(funcp);
            }
        }
        stable_sort(funcps.begin(), funcps.end(),
                    [](const AstNode* ap, const AstNode* bp) { return ap->name() < bp->name(); });
        return funcps;
    }

    void putSectionDelimiter(const string& name) {
        puts("\n");
        puts("//============================================================\n");
        puts("// " + name + "\n");
    }

    void emitHeader(AstNodeModule* modp) {
        UASSERT(!m_ofp, "Output file should not be open");

        const string filename = v3Global.opt.makeDir() + "/" + topClassName() + ".h";
        newCFile(filename, /* slow: */ false, /* source: */ false);
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile(filename) : new V3OutCFile(filename);

        ofp()->putsHeader();
        puts("// DESCRIPTION: Verilator output: Primary model header\n");
        puts("//\n");
        puts("// This header should be included by all source files instantiating the design.\n");
        puts("// The class here is then constructed to instantiate the design.\n");
        puts("// See the Verilator manual for examples.\n");

        ofp()->putsGuard();

        // Include files
        puts("\n");
        ofp()->putsIntTopInclude();
        puts("#include \"verilated.h\"\n");
        if (v3Global.opt.mtasks()) puts("#include \"verilated_threads.h\"\n");
        if (v3Global.opt.savable()) puts("#include \"verilated_save.h\"\n");
        if (v3Global.opt.coverage()) puts("#include \"verilated_cov.h\"\n");
        if (v3Global.dpi()) puts("#include \"svdpi.h\"\n");

        // Declare foreign instances up front to make C++ happy
        puts("\n");
        puts("class " + symClassName() + ";\n");
        puts("class " + prefixNameProtect(modp) + ";\n");  // For rootp pointer only
        if (v3Global.opt.trace()) puts("class " + v3Global.opt.traceClassLang() + ";\n");
        emitModCUse(modp, VUseType::INT_FWD_CLASS);  // Note: This is needed for cell forwarding

        puts("\n");

        puts("// This class is the main interface to the Verilated model\n");
        puts("class " + topClassName() + " VL_NOT_FINAL : ");
        if (optSystemC()) {
            // SC_MODULE, but with multiple-inheritance of VerilatedModel
            puts("public ::sc_core::sc_module, ");
        }
        puts("public VerilatedModel {\n");
        ofp()->resetPrivate();
        ofp()->putsPrivate(true);  // private:

        puts("// Symbol table holding complete model state (owned by this class)\n");
        puts(symClassName() + "* const vlSymsp;\n");

        puts("\n");
        ofp()->putsPrivate(false);  // public:
        // User accessible IO
        puts("\n// PORTS\n"
             "// The application code writes and reads these signals to\n"
             "// propagate new values into/out from the Verilated model.\n");
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isPrimaryIO()) {  //
                    emitVarDecl(varp, /* asRef: */ true);
                }
            }
        }

        // Cells instantiated by the top level (for access to /* verilator public */)
        puts("\n// CELLS\n"
             "// Public to allow access to /* verilator public */ items.\n"
             "// Otherwise the application code can consider these internals.\n");
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                puts(prefixNameProtect(cellp->modp()) + "* const " + cellp->nameProtect() + ";\n");
            }
        }

        // root instance pointer (for access to internals, including public_flat items).
        puts("\n// Root instance pointer to allow access to model internals,\n"
             "// including inlined /* verilator public_flat_* */ items.\n");
        puts(prefixNameProtect(modp) + "* const rootp;\n");

        puts("\n");
        ofp()->putsPrivate(false);  // public:
        puts("// CONSTRUCTORS\n");
        if (optSystemC()) {
            puts("SC_CTOR(" + topClassName() + ");\n");
            puts("virtual ~" + topClassName() + "();\n");
        } else {
            puts("/// Construct the model; called by application code\n");
            puts("/// If contextp is null, then the model will use the default global "
                 "context\n");
            puts("/// If name is \"\", then makes a wrapper with a\n");
            puts("/// single model invisible with respect to DPI scope names.\n");
            puts("explicit " + topClassName() + "(VerilatedContext* contextp,"
                 + " const char* name = \"TOP\");\n");
            puts("explicit " + topClassName() + "(const char* name = \"TOP\");\n");
            puts("/// Destroy the model; called (often implicitly) by application code\n");
            puts("virtual ~" + topClassName() + "();\n");
        }
        ofp()->putsPrivate(true);
        puts("VL_UNCOPYABLE(" + topClassName() + ");  ///< Copying not allowed\n");

        puts("\n");
        ofp()->putsPrivate(false);  // public:
        puts("// API METHODS\n");
        const string callEvalEndStep
            = (v3Global.needTraceDumper() && !optSystemC()) ? "eval_end_step(); " : "";
        if (optSystemC()) {
            ofp()->putsPrivate(true);  ///< eval() is invoked by our sensitive() calls.
        }
        if (!optSystemC()) {
            puts("/// Evaluate the model.  Application must call when inputs change.\n");
        }
        puts("void eval() { eval_step(); " + callEvalEndStep + "}\n");
        if (!optSystemC()) {
            puts("/// Evaluate when calling multiple units/models per time step.\n");
        }
        puts("void eval_step();\n");
        if (!optSystemC()) {
            puts("/// Evaluate at end of a timestep for tracing, when using eval_step().\n");
            puts("/// Application must call after all eval() and before time changes.\n");
            puts("void eval_end_step()");
            if (callEvalEndStep == "") {
                puts(" {}\n");
            } else {
                puts(";\n");
            }
        }
        if (!optSystemC()) {
            puts("/// Simulation complete, run final blocks.  Application "
                 "must call on completion.\n");
        }
        ofp()->putsPrivate(false);  // public:
        puts("void final();\n");

        if (v3Global.opt.trace()) {
            puts("/// Trace signals in the model; called by application code\n");
            puts("void trace(" + v3Global.opt.traceClassBase()
                 + "C* tfp, int levels, int options = 0);\n");
            if (optSystemC()) {
                puts("/// SC tracing; avoid overloaded virtual function lint warning\n");
                puts("virtual void trace(sc_trace_file* tfp) const override { "
                     "::sc_core::sc_module::trace(tfp); }\n");
            }
        }

        if (!optSystemC()) {
            puts("/// Retrieve name of this model instance (as passed to constructor).\n");
            puts("const char* name() const;\n");
        }

        // Emit DPI export dispatcher declarations
        {
            const CFuncVector funcps
                = findFuncps([](const AstCFunc* nodep) { return nodep->dpiExportDispatcher(); });
            if (!funcps.empty()) {
                puts("\n/// DPI Export functions\n");
                for (const AstCFunc* funcp : funcps) emitCFuncDecl(funcp, modp);
            }
        }

        if (v3Global.opt.savable()) {
            puts("\n");
            puts("// Serialization functions\n");
            puts("friend VerilatedSerialize& operator<<(VerilatedSerialize& os, "  //
                 + topClassName() + "& rhs);\n");
            puts("friend VerilatedDeserialize& operator>>(VerilatedDeserialize& os, "
                 + topClassName() + "& rhs);\n");
        }

        puts("\n// Abstract methods from VerilatedModel\n");
        puts("const char* hierName() const override final;\n");
        puts("const char* modelName() const override final;\n");
        puts("unsigned threads() const override final;\n");
        if (v3Global.opt.trace()) {
            puts("std::unique_ptr<VerilatedTraceConfig> traceConfig() const override final;\n");
        }

        puts("} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);\n");

        ofp()->putsEndGuard();

        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }

    void emitConstructorImplementation(AstNodeModule* modp) {
        putSectionDelimiter("Constructors");

        puts("\n");
        puts(topClassName() + "::" + topClassName());
        if (optSystemC()) {
            puts("(sc_module_name /* unused */)\n");
            puts("    : VerilatedModel{*Verilated::threadContextp()}\n");
            puts("    , vlSymsp{new " + symClassName() + "(contextp(), name(), this)}\n");
        } else {
            puts(+"(VerilatedContext* _vcontextp__, const char* _vcname__)\n");
            puts("    : VerilatedModel{*_vcontextp__}\n");
            puts("    , vlSymsp{new " + symClassName() + "(contextp(), _vcname__, this)}\n");
        }

        // Set up IO references
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isPrimaryIO()) {
                    const string protName = varp->nameProtect();
                    puts("    , " + protName + "{vlSymsp->TOP." + protName + "}\n");
                }
            }
        }

        // Setup cell pointers
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                const string protName = cellp->nameProtect();
                puts("    , " + protName + "{vlSymsp->TOP." + protName + "}\n");
            }
        }

        // Setup rootp root instance pointer,
        puts("    , rootp{&(vlSymsp->TOP)}\n");

        puts("{\n");
        puts("// Register model with the context\n");
        puts("contextp()->addModel(this);\n");

        if (optSystemC()) {
            // Create sensitivity list for when to evaluate the model.
            putsDecoration("// Sensitivities on all clocks and combinational inputs\n");
            puts("SC_METHOD(eval);\n");
            for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                    if (varp->isNonOutput() && (varp->isScSensitive() || varp->isUsedClock())) {
                        int vects = 0;
                        // This isn't very robust and may need cleanup for other data types
                        for (AstUnpackArrayDType* arrayp
                             = VN_CAST(varp->dtypeSkipRefp(), UnpackArrayDType);
                             arrayp;
                             arrayp = VN_CAST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
                            const int vecnum = vects++;
                            UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                        "Should have swapped msb & lsb earlier.");
                            const string ivar = std::string{"__Vi"} + cvtToStr(vecnum);
                            puts("for (int __Vi" + cvtToStr(vecnum) + "="
                                 + cvtToStr(arrayp->lo()));
                            puts("; " + ivar + "<=" + cvtToStr(arrayp->hi()));
                            puts("; ++" + ivar + ") {\n");
                        }
                        puts("sensitive << " + varp->nameProtect());
                        for (int v = 0; v < vects; ++v) puts("[__Vi" + cvtToStr(v) + "]");
                        puts(";\n");
                        for (int v = 0; v < vects; ++v) puts("}\n");
                    }
                }
            }
            puts("\n");
        }

        puts("}\n");

        if (!optSystemC()) {
            puts("\n");
            puts(topClassName() + "::" + topClassName() + "(const char* _vcname__)\n");
            puts("    : " + topClassName() + "(Verilated::threadContextp(), _vcname__)\n{\n}\n");
        }
    }

    void emitDestructorImplementation() {
        putSectionDelimiter("Destructor");

        puts("\n");
        puts(topClassName() + "::~" + topClassName() + "() {\n");
        puts("delete vlSymsp;\n");
        puts("}\n");
    }

    void emitSettleLoop(AstNodeModule* modp, bool initial) {
        const string topModNameProtected = prefixNameProtect(modp);

        putsDecoration("// Evaluate till stable\n");
        if (v3Global.rootp()->changeRequest()) {
            puts("int __VclockLoop = 0;\n");
            puts("QData __Vchange = 1;\n");
        }
        if (v3Global.opt.trace()) puts("vlSymsp->__Vm_activity = true;\n");
        puts("do {\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+ ");
        puts(initial ? "Initial" : "Clock");
        puts(" loop\\n\"););\n");
        if (initial)
            puts(topModNameProtected + "__" + protect("_eval_settle") + "(&(vlSymsp->TOP));\n");

        if (v3Global.opt.profExec() && !initial) {
            puts("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).evalLoopBegin();\n");
        }

        puts(topModNameProtected + "__" + protect("_eval") + "(&(vlSymsp->TOP));\n");

        if (v3Global.opt.profExec() && !initial) {
            puts("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).evalLoopEnd();\n");
        }

        if (v3Global.rootp()->changeRequest()) {
            puts("if (VL_UNLIKELY(++__VclockLoop > " + cvtToStr(v3Global.opt.convergeLimit())
                 + ")) {\n");
            puts("// About to fail, so enable debug to see what's not settling.\n");
            puts("// Note you must run make with OPT=-DVL_DEBUG for debug prints.\n");
            puts("int __Vsaved_debug = Verilated::debug();\n");
            puts("Verilated::debug(1);\n");
            puts("__Vchange = " + topModNameProtected + "__" + protect("_change_request")
                 + "(&(vlSymsp->TOP));\n");
            puts("Verilated::debug(__Vsaved_debug);\n");
            puts("VL_FATAL_MT(");
            putsQuoted(protect(modp->fileline()->filename()));
            puts(", ");
            puts(cvtToStr(modp->fileline()->lineno()));
            puts(", \"\",\n");
            puts("\"Verilated model didn't ");
            if (initial) puts("DC ");
            puts("converge\\n\"\n");
            puts("\"- See https://verilator.org/warn/DIDNOTCONVERGE\");\n");
            puts("} else {\n");
            puts("__Vchange = " + topModNameProtected + "__" + protect("_change_request")
                 + "(&(vlSymsp->TOP));\n");
            puts("}\n");
        }
        puts("} while ("
             + (v3Global.rootp()->changeRequest() ? std::string{"VL_UNLIKELY(__Vchange)"}
                                                  : std::string{"0"})
             + ");\n");
    }

    void emitStandardMethods1(AstNodeModule* modp) {
        UASSERT_OBJ(modp->isTop(), modp, "Attempting to emitWrapEval for non-top class");

        const string topModNameProtected = prefixNameProtect(modp);
        const string selfDecl = "(" + topModNameProtected + "* vlSelf)";

        putSectionDelimiter("Evaluation loop");

        // Forward declarations
        puts("\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_initial") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_settle") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval") + selfDecl + ";\n");
        if (v3Global.rootp()->changeRequest()) {
            puts("QData " + topModNameProtected + "__" + protect("_change_request") + selfDecl
                 + ";\n");
        }
        puts("#ifdef VL_DEBUG\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_debug_assertions") + selfDecl
             + ";\n");
        puts("#endif  // VL_DEBUG\n");
        puts("void " + topModNameProtected + "__" + protect("_final") + selfDecl + ";\n");

        // _eval_initial_loop
        puts("\nstatic void " + protect("_eval_initial_loop") + "(" + symClassVar() + ")"
             + " {\n");
        puts("vlSymsp->__Vm_didInit = true;\n");
        puts(topModNameProtected + "__" + protect("_eval_initial") + "(&(vlSymsp->TOP));\n");
        emitSettleLoop(modp, /* initial: */ true);
        ensureNewLine();
        puts("}\n");
    }

    void emitStandardMethods2(AstNodeModule* modp) {
        const string topModNameProtected = prefixNameProtect(modp);
        // ::eval_step
        puts("\nvoid " + topClassName() + "::eval_step() {\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+++++TOP Evaluate " + topClassName()
             + "::eval_step\\n\"); );\n");

        puts("#ifdef VL_DEBUG\n");
        putsDecoration("// Debug assertions\n");
        puts(topModNameProtected + "__" + protect("_eval_debug_assertions")
             + "(&(vlSymsp->TOP));\n");
        puts("#endif  // VL_DEBUG\n");

        putsDecoration("// Initialize\n");
        puts("if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) " + protect("_eval_initial_loop")
             + "(vlSymsp);\n");

        if (v3Global.opt.threads() == 1) {
            const uint32_t mtaskId = 0;
            putsDecoration("// MTask " + cvtToStr(mtaskId) + " start\n");
            puts("VL_DEBUG_IF(VL_DBG_MSGF(\"MTask" + cvtToStr(mtaskId) + " starting\\n\"););\n");
            puts("Verilated::mtaskId(" + cvtToStr(mtaskId) + ");\n");
        }

        if (v3Global.opt.profExec()) {
            puts("vlSymsp->__Vm_executionProfilerp->configure();\n");
            puts("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).evalBegin();\n");
        }

        emitSettleLoop(modp, /* initial: */ false);

        putsDecoration("// Evaluate cleanup\n");
        if (v3Global.opt.threads() == 1) {
            puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");
        }
        if (v3Global.opt.threads()) puts("Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);\n");

        if (v3Global.opt.profExec()) puts("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).evalEnd();\n");
        puts("}\n");
    }

    void emitStandardMethods3(AstNodeModule* modp) {
        const string topModNameProtected = prefixNameProtect(modp);
        // ::eval_end_step
        if (v3Global.needTraceDumper() && !optSystemC()) {
            puts("\nvoid " + topClassName() + "::eval_end_step() {\n");
            puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+eval_end_step " + topClassName()
                 + "::eval_end_step\\n\"); );\n");
            puts("#ifdef VM_TRACE\n");
            putsDecoration("// Tracing\n");
            // SystemC's eval loop deals with calling trace, not us
            puts("if (VL_UNLIKELY(vlSymsp->__Vm_dumping)) vlSymsp->_traceDump();\n");
            puts("#endif  // VM_TRACE\n");
            puts("}\n");
        }

        putSectionDelimiter("Utilities");

        if (!optSystemC()) {
            // ::name
            puts("\nconst char* " + topClassName() + "::name() const {\n");
            puts(/**/ "return vlSymsp->name();\n");
            puts("}\n");
        }

        putSectionDelimiter("Invoke final blocks");
        // ::final
        puts("\nVL_ATTR_COLD void " + topClassName() + "::final() {\n");
        puts(/**/ topModNameProtected + "__" + protect("_final") + "(&(vlSymsp->TOP));\n");
        puts("}\n");

        putSectionDelimiter("Implementations of abstract methods from VerilatedModel\n");
        puts("const char* " + topClassName() + "::hierName() const { return vlSymsp->name(); }\n");
        puts("const char* " + topClassName() + "::modelName() const { return \"" + topClassName()
             + "\"; }\n");
        puts("unsigned " + topClassName() + "::threads() const { return "
             + cvtToStr(std::max(1, v3Global.opt.threads())) + "; }\n");

        if (v3Global.opt.trace()) {
            puts("std::unique_ptr<VerilatedTraceConfig> " + topClassName()
                 + "::traceConfig() const {\n");
            puts("return std::unique_ptr<VerilatedTraceConfig>{new VerilatedTraceConfig{");
            puts(v3Global.opt.useTraceParallel() ? "true" : "false");
            puts(v3Global.opt.useTraceOffload() ? ", true" : ", false");
            puts(v3Global.opt.useFstWriterThread() ? ", true" : ", false");
            puts("}};\n");
            puts("};\n");
        }
    }

    void emitTraceMethods(AstNodeModule* modp) {
        const string topModNameProtected = prefixNameProtect(modp);

        putSectionDelimiter("Trace configuration");

        // Forward declaration
        puts("\nvoid " + topModNameProtected + "__" + protect("trace_init_top") + "("
             + topModNameProtected + "* vlSelf, " + v3Global.opt.traceClassBase()
             + "* tracep);\n");

        // Static helper function
        puts("\nVL_ATTR_COLD static void " + protect("trace_init") + "(void* voidSelf, "
             + v3Global.opt.traceClassBase() + "* tracep, uint32_t code) {\n");
        putsDecoration("// Callback from tracep->open()\n");
        puts(voidSelfAssign(modp));
        puts(symClassAssign());
        puts("if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {\n");
        puts("VL_FATAL_MT(__FILE__, __LINE__, __FILE__,\n");
        puts("\"Turning on wave traces requires Verilated::traceEverOn(true) call before time "
             "0.\");\n");
        puts("}\n");
        puts("vlSymsp->__Vm_baseCode = code;\n");
        puts("tracep->scopeEscape(' ');\n");
        puts("tracep->pushNamePrefix(std::string{vlSymsp->name()} + ' ');\n");
        puts(topModNameProtected + "__" + protect("trace_init_top") + "(vlSelf, tracep);\n");
        puts("tracep->popNamePrefix();\n");
        puts("tracep->scopeEscape('.');\n");  // Restore so later traced files won't break
        puts("}\n");

        // Forward declaration
        puts("\nVL_ATTR_COLD void " + topModNameProtected + "__" + protect("trace_register") + "("
             + topModNameProtected + "* vlSelf, " + v3Global.opt.traceClassBase()
             + "* tracep);\n");

        const CFuncVector traceInitFuncps
            = findFuncps([](const AstCFunc* nodep) { return nodep->dpiTraceInit(); });
        for (const AstCFunc* const funcp : traceInitFuncps) emitCFuncDecl(funcp, modp);

        // ::trace
        puts("\nVL_ATTR_COLD void " + topClassName() + "::trace(");
        puts(v3Global.opt.traceClassBase() + "C* tfp, int levels, int options) {\n");
        if (optSystemC()) {
            puts(/**/ "if (!sc_core::sc_get_curr_simcontext()->elaboration_done()) {\n");
            puts(/****/ "vl_fatal(__FILE__, __LINE__, name(), \"" + topClassName()
                 + +"::trace() is called before sc_core::sc_start(). "
                    "Run sc_core::sc_start(sc_core::SC_ZERO_TIME) before trace() to complete "
                    "elaboration.\");\n");
            puts(/**/ "}");
        }
        puts(/**/ "if (false && levels && options) {}  // Prevent unused\n");
        puts(/**/ "tfp->spTrace()->addModel(this);\n");
        puts(/**/ "tfp->spTrace()->addInitCb(&" + protect("trace_init") + ", &(vlSymsp->TOP));\n");
        puts(/**/ topModNameProtected + "__" + protect("trace_register")
             + "(&(vlSymsp->TOP), tfp->spTrace());\n");

        if (!traceInitFuncps.empty()) {
            puts(/**/ "if (levels > 0) {\n");
            puts(/****/ "const QData tfpq = reinterpret_cast<QData>(tfp);\n");
            for (const AstCFunc* const funcp : traceInitFuncps) {
                // Some hackery to locate handle__V for trace_init_task
                // Considered a pragma on the handle, but that still doesn't help us attach it here
                string handle = funcp->name();
                const size_t wr_len = strlen("__Vdpiimwrap_");
                UASSERT_OBJ(handle.substr(0, wr_len) == "__Vdpiimwrap_", funcp,
                            "Strange trace_init_task function name");
                handle = "vlSymsp->TOP." + handle.substr(wr_len);
                const string::size_type pos = handle.rfind("__DOT__");
                UASSERT_OBJ(pos != string::npos, funcp, "Strange trace_init_task function name");
                handle = handle.substr(0, pos) + "__DOT__handle___05FV";
                puts(funcNameProtect(funcp, modp) + "(" + handle
                     + ", tfpq, levels - 1, options);\n");
            }
            puts(/**/ "}\n");
        }

        puts("}\n");
    }

    void emitSerializationFunctions() {
        putSectionDelimiter("Model serialization");

        puts("\nVerilatedSerialize& operator<<(VerilatedSerialize& os, " + topClassName()
             + "& rhs) {\n");
        puts(/**/ "Verilated::quiesce();\n");
        puts(/**/ "rhs.vlSymsp->" + protect("__Vserialize") + "(os);\n");
        puts(/**/ "return os;\n");
        puts("}\n");

        puts("\nVerilatedDeserialize& operator>>(VerilatedDeserialize& os, " + topClassName()
             + "& rhs) {\n");
        puts(/**/ "Verilated::quiesce();\n");
        puts(/**/ "rhs.vlSymsp->" + protect("__Vdeserialize") + "(os);\n");
        puts(/**/ "return os;\n");
        puts("}\n");
    }

    void emitImplementation(AstNodeModule* modp) {
        UASSERT(!m_ofp, "Output file should not be open");

        const string filename = v3Global.opt.makeDir() + "/" + topClassName() + ".cpp";
        newCFile(filename, /* slow: */ false, /* source: */ true);
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile(filename) : new V3OutCFile(filename);

        ofp()->putsHeader();
        puts("// DESCRIPTION: Verilator output: "
             "Model implementation (design independent parts)\n");

        puts("\n");
        puts("#include \"" + topClassName() + ".h\"\n");
        puts("#include \"" + symClassName() + ".h\"\n");
        if (v3Global.opt.trace()) {
            puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
        }
        if (v3Global.dpi()) {  //
            puts("#include \"verilated_dpi.h\"\n");
        }

        emitConstructorImplementation(modp);
        emitDestructorImplementation();
        emitStandardMethods1(modp);
        emitStandardMethods2(modp);
        emitStandardMethods3(modp);
        if (v3Global.opt.trace()) { emitTraceMethods(modp); }
        if (v3Global.opt.savable()) { emitSerializationFunctions(); }

        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }

    void emitDpiExportDispatchers(AstNodeModule* modp) {
        UASSERT(!m_ofp, "Output file should not be open");

        // Emit DPI Export dispatchers
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            AstCFunc* const funcp = VN_CAST(nodep, CFunc);
            if (!funcp || !funcp->dpiExportDispatcher()) continue;

            if (splitNeeded()) {
                // Splitting file, so using parallel build.
                v3Global.useParallelBuild(true);
                // Close old file
                VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
            }

            if (!m_ofp) {
                string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__Dpi_Export";
                filename = m_uniqueNames.get(filename);
                filename += ".cpp";
                newCFile(filename, /* slow: */ false, /* source: */ true);
                m_ofp = v3Global.opt.systemC() ? new V3OutScFile{filename}
                                               : new V3OutCFile{filename};
                splitSizeReset();  // Reset file size tracking
                m_lazyDecls.reset();
                m_ofp->putsHeader();
                puts(
                    "// DESCRIPTION: Verilator output: Implementation of DPI export functions.\n");
                puts("//\n");
                puts("#include \"" + topClassName() + ".h\"\n");
                puts("#include \"" + symClassName() + ".h\"\n");
                puts("#include \"verilated_dpi.h\"\n");
                puts("\n");
            }

            iterate(funcp);
        }

        if (m_ofp) { VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr); }
    }

    void main(AstNodeModule* modp) {
        m_modp = modp;
        emitHeader(modp);
        emitImplementation(modp);
        if (v3Global.dpi()) { emitDpiExportDispatchers(modp); }
    }

    // VISITORS

public:
    explicit EmitCModel(AstNetlist* netlistp) { main(netlistp->topModulep()); }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcModel() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { EmitCModel{v3Global.rootp()}; }
}
