// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for model entry point class
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCFunc.h"

#include <algorithm>
#include <vector>

class EmitCModel final : public EmitCFunc {

    // METHODS
    VL_DEBUG_FUNC;

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
        puts("#include \"verilated_heavy.h\"\n");
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
        if (optSystemC()) {
            puts("SC_MODULE(" + topClassName() + ") {\n");
        } else {
            puts("class " + topClassName() + " VL_NOT_FINAL {\n");
        }
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
            if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) {
                if (varp->isPrimaryIO()) {  //
                    emitVarDecl(varp, "", /* asRef: */ true);
                }
            }
        }

        // Cells instantiated by the top level (for access to /* verilator public */)
        puts("\n// CELLS\n"
             "// Public to allow access to /* verilator public */ items.\n"
             "// Otherwise the application code can consider these internals.\n");
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST_CONST(nodep, Cell)) {
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
        string callEvalEndStep
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

        puts("/// Return current simulation context for this model.\n");
        puts("/// Used to get to e.g. simulation time via contextp()->time()\n");
        puts("VerilatedContext* contextp() const;\n");
        if (!optSystemC()) {
            puts("/// Retrieve name of this model instance (as passed to constructor).\n");
            puts("const char* name() const;\n");
        }

        // Emit DPI export dispatcher declarations
        {
            std::vector<const AstCFunc*> funcps;

            for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstCFunc* funcp = VN_CAST(nodep, CFunc)) {
                    if (!funcp->dpiExportDispatcher()) continue;
                    funcps.push_back(funcp);
                }
            }

            stable_sort(funcps.begin(), funcps.end(), [](const AstNode* ap, const AstNode* bp) {
                return ap->name() < bp->name();
            });

            if (!funcps.empty()) {
                puts("\n/// DPI Export functions\n");
                for (const AstCFunc* funcp : funcps) { emitCFuncDecl(funcp, modp); }
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
            puts("    : vlSymsp{new " + symClassName() + "(nullptr, name(), this)}\n");
        } else {
            puts(+"(VerilatedContext* _vcontextp__, const char* _vcname__)\n");
            puts("    : vlSymsp{new " + symClassName() + "(_vcontextp__, _vcname__, this)}\n");
        }

        // Set up IO references
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) {
                if (varp->isPrimaryIO()) {
                    const string protName = varp->nameProtect();
                    puts("    , " + protName + "{vlSymsp->TOP." + protName + "}\n");
                }
            }
        }

        // Setup cell pointers
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST_CONST(nodep, Cell)) {
                const string protName = cellp->nameProtect();
                puts("    , " + protName + "{vlSymsp->TOP." + protName + "}\n");
            }
        }

        // Setup rootp root instance pointer,
        puts("    , rootp{&(vlSymsp->TOP)}\n");

        puts("{\n");

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
                            const string ivar = string("__Vi") + cvtToStr(vecnum);
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
            puts("    : " + topClassName() + "(nullptr, _vcname__)\n{\n}\n");
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
        puts("int __VclockLoop = 0;\n");
        puts("QData __Vchange = 1;\n");
        if (v3Global.opt.trace()) puts("vlSymsp->__Vm_activity = true;\n");
        puts("do {\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+ ");
        puts(initial ? "Initial" : "Clock");
        puts(" loop\\n\"););\n");
        if (initial)
            puts(topModNameProtected + "__" + protect("_eval_settle") + "(&(vlSymsp->TOP));\n");
        puts(topModNameProtected + "__" + protect("_eval") + "(&(vlSymsp->TOP));\n");
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
        puts("} while (VL_UNLIKELY(__Vchange));\n");
    }

    void emitStandardMethods(AstNodeModule* modp) {
        UASSERT_OBJ(modp->isTop(), modp, "Attempting to emitWrapEval for non-top class");

        const string topModNameProtected = prefixNameProtect(modp);
        const string selfDecl = "(" + topModNameProtected + "* vlSelf)";

        putSectionDelimiter("Evaluation loop");

        // Forward declarations
        puts("\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_initial") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_settle") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval") + selfDecl + ";\n");
        puts("QData " + topModNameProtected + "__" + protect("_change_request") + selfDecl
             + ";\n");
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
            uint32_t mtaskId = 0;
            putsDecoration("// MTask " + cvtToStr(mtaskId) + " start\n");
            puts("VL_DEBUG_IF(VL_DBG_MSGF(\"MTask" + cvtToStr(mtaskId) + " starting\\n\"););\n");
            puts("Verilated::mtaskId(" + cvtToStr(mtaskId) + ");\n");
        }

        if (v3Global.opt.mtasks() && v3Global.opt.profThreads()) {
            puts("if (VL_UNLIKELY((vlSymsp->_vm_contextp__->profThreadsStart() != "
                 "vlSymsp->__Vm_profile_time_finished)\n");
            puts(" && (VL_TIME_Q() > vlSymsp->_vm_contextp__->profThreadsStart())\n");
            puts(" && (vlSymsp->_vm_contextp__->profThreadsWindow() >= 1))) {\n");
            // Within a profile (either starting, middle, or end)
            puts("if (vlSymsp->__Vm_profile_window_ct == 0) {\n");  // Opening file?
            // Start profile on this cycle. We'll capture a window worth, then
            // only analyze the next window worth. The idea is that the first window
            // capture will hit some cache-cold stuff (eg printf) but it'll be warm
            // by the time we hit the second window, we hope.
            puts("vlSymsp->__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
            // "* 2" as first half is warmup, second half is collection
            puts("vlSymsp->__Vm_profile_window_ct = vlSymsp->_vm_contextp__->profThreadsWindow() "
                 "* 2 "
                 "+ "
                 "1;\n");
            puts("}\n");
            puts("--(vlSymsp->__Vm_profile_window_ct);\n");
            puts("if (vlSymsp->__Vm_profile_window_ct == "
                 "vlSymsp->_vm_contextp__->profThreadsWindow()) {\n");
            // This barrier record in every threads' profile demarcates the
            // cache-warm-up cycles before the barrier from the actual profile
            // cycles afterward.
            puts("vlSymsp->__Vm_threadPoolp->profileAppendAll(");
            puts("VlProfileRec(VlProfileRec::Barrier()));\n");
            puts("vlSymsp->__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
            puts("}\n");
            puts("else if (vlSymsp->__Vm_profile_window_ct == 0) {\n");
            // Ending file.
            puts("vluint64_t elapsed = VL_RDTSC_Q() - vlSymsp->__Vm_profile_cycle_start;\n");
            puts("vlSymsp->__Vm_threadPoolp->profileDump(vlSymsp->_vm_contextp__->"
                 "profThreadsFilename().c_str(), elapsed);\n");
            // This turns off the test to enter the profiling code, but still
            // allows the user to collect another profile by changing
            // profThreadsStart
            puts("vlSymsp->__Vm_profile_time_finished = "
                 "vlSymsp->_vm_contextp__->profThreadsStart();\n");
            puts("vlSymsp->__Vm_profile_cycle_start = 0;\n");
            puts("}\n");
            puts("}\n");
        }

        emitSettleLoop(modp, /* initial: */ false);
        if (v3Global.opt.threads() == 1) {
            puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");
        }
        if (v3Global.opt.threads()) puts("Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);\n");
        puts("}\n");

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

        putSectionDelimiter("Invoke final blocks");
        // ::final
        puts("\nvoid " + topClassName() + "::final() {\n");
        puts(topModNameProtected + "__" + protect("_final") + "(&(vlSymsp->TOP));\n");
        puts("}\n");

        putSectionDelimiter("Utilities");
        // ::contextp
        puts("\nVerilatedContext* " + topClassName() + "::contextp() const {\n");
        puts(/**/ "return vlSymsp->_vm_contextp__;\n");
        puts("}\n");

        if (!optSystemC()) {
            // ::name
            puts("\nconst char* " + topClassName() + "::name() const {\n");
            puts(/**/ "return vlSymsp->name();\n");
            puts("}\n");
        }
    }

    void emitTraceMethods(AstNodeModule* modp) {
        const string topModNameProtected = prefixNameProtect(modp);

        putSectionDelimiter("Trace configuration");

        // Forward declaration
        puts("\nvoid " + topModNameProtected + "__" + protect("traceInitTop") + "("
             + topModNameProtected + "* vlSelf, " + v3Global.opt.traceClassBase()
             + "* tracep);\n");

        // Static helper function
        puts("\nstatic void " + protect("traceInit") + "(void* voidSelf, "
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
        puts("tracep->module(vlSymsp->name());\n");
        puts("tracep->scopeEscape(' ');\n");
        puts(topModNameProtected + "__" + protect("traceInitTop") + "(vlSelf, tracep);\n");
        puts("tracep->scopeEscape('.');\n");  // Restore so later traced files won't break
        puts("}\n");

        // Forward declaration
        puts("\nvoid " + topModNameProtected + "__" + protect("traceRegister") + "("
             + topModNameProtected + "* vlSelf, " + v3Global.opt.traceClassBase()
             + "* tracep);\n");

        // ::trace
        puts("\nvoid " + topClassName() + "::trace(");
        puts(v3Global.opt.traceClassBase() + "C* tfp, int, int) {\n");
        puts("tfp->spTrace()->addInitCb(&" + protect("traceInit") + ", &(vlSymsp->TOP));\n");
        puts(topModNameProtected + "__" + protect("traceRegister")
             + "(&(vlSymsp->TOP), tfp->spTrace());\n");
        puts("}\n");
    }

    void emitSerializationFunctions() {
        putSectionDelimiter("Model serialization");

        puts("\nVerilatedSerialize& operator<<(VerilatedSerialize& os, " + topClassName()
             + "& rhs) {\n");
        puts("Verilated::quiesce();\n");
        puts("rhs.vlSymsp->" + protect("__Vserialize") + "(os);\n");
        puts("return os;\n");
        puts("}\n");

        puts("\nVerilatedDeserialize& operator>>(VerilatedDeserialize& os, " + topClassName()
             + "& rhs) {\n");
        puts("Verilated::quiesce();\n");
        puts("rhs.vlSymsp->" + protect("__Vdeserialize") + "(os);\n");
        puts("return os;\n");
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
        emitStandardMethods(modp);
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
                const string filename = v3Global.opt.makeDir() + "/" + topClassName()
                                        + "__Dpi_Export_" + cvtToStr(splitFilenumInc() - 1)
                                        + ".cpp";
                newCFile(filename, /* slow: */ false, /* source: */ true);
                m_ofp = v3Global.opt.systemC() ? new V3OutScFile(filename)
                                               : new V3OutCFile(filename);
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
    { EmitCModel emit(v3Global.rootp()); }
}
