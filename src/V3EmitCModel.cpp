// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for model entry point class
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitC.h"
#include "V3EmitCFunc.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <functional>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class EmitCModel final : public EmitCFunc {
    // TYPES
    using CFuncVector = std::vector<const AstCFunc*>;

    // MEMBERS
    V3UniqueNames m_uniqueNames;  // For generating unique file names

    // METHODS
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
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};

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
        putns(modp, "class alignas(VL_CACHE_LINE_BYTES) " + topClassName() + " VL_NOT_FINAL : ");
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

        puts("\n// CONSTEXPR CAPABILITIES\n");
        puts("// Verilated with --trace?\n");
        puts("static constexpr bool traceCapable = "s
             + (v3Global.opt.trace() ? "true;\n"s : "false;\n"s));

        // User accessible IO
        puts("\n// PORTS\n"
             "// The application code writes and reads these signals to\n"
             "// propagate new values into/out from the Verilated model.\n");
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isPrimaryIO()) {  //
                    emitVarDecl(varp, /* asRef: */ true);
                    if(v3Global.opt.emitAccessors()) {
                        emitVarAccessors(varp);
                    }
                }
            }
        }
        if (optSystemC() && v3Global.usesTiming()) puts("sc_core::sc_event trigger_eval;\n");

        // Cells instantiated by the top level (for access to /* verilator public */)
        puts("\n// CELLS\n"
             "// Public to allow access to /* verilator public */ items.\n"
             "// Otherwise the application code can consider these internals.\n");
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                putns(cellp, prefixNameProtect(cellp->modp()) + "* const " + cellp->nameProtect()
                                 + ";\n");
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
        if (optSystemC() && v3Global.usesTiming()) {
            puts("void eval();\n");
            puts("void eval_sens();\n");
        } else {
            puts("void eval() { eval_step(); " + callEvalEndStep + "}\n");
        }
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

        puts("/// Are there scheduled events to handle?\n");
        puts("bool eventsPending();\n");
        puts("/// Returns time at next time slot. Aborts if !eventsPending()\n");
        puts("uint64_t nextTimeSlot();\n");

        if (v3Global.opt.trace() || !optSystemC()) {
            puts("/// Trace signals in the model; called by application code\n");
            // Backward-compatible usage of calling trace() on the model - now part of context
            puts("void trace(VerilatedTraceBaseC* tfp, int levels, int options = 0) {"
                 " contextp()->trace(tfp, levels, options); }\n");
        }
        if (v3Global.opt.trace() && optSystemC()) {
            puts("/// SC tracing; avoid overloaded virtual function lint warning\n");
            puts("void trace(sc_core::sc_trace_file* tfp) const override { "
                 "::sc_core::sc_module::trace(tfp); }\n");
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
        puts("/// Prepare for cloning the model at the process level (e.g. fork in Linux)\n");
        puts("/// Release necessary resources. Called before cloning.\n");
        puts("void prepareClone() const;\n");
        puts("/// Re-init after cloning the model at the process level (e.g. fork in Linux)\n");
        puts("/// Re-allocate necessary resources. Called after cloning.\n");
        puts("void atClone() const;\n");
        if (v3Global.opt.trace()) {
            puts("std::unique_ptr<VerilatedTraceConfig> traceConfig() const override final;\n");
        }

        ofp()->putsPrivate(true);  // private:
        puts("// Internal functions - trace registration\n");
        puts("void traceBaseModel(VerilatedTraceBaseC* tfp, int levels, int options);\n");

        puts("};\n");

        ofp()->putsEndGuard();

        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }

    void emitConstructorImplementation(AstNodeModule* modp) {
        putSectionDelimiter("Constructors");

        puts("\n");
        putns(modp, topClassName() + "::" + topClassName());
        if (optSystemC()) {
            puts("(sc_core::sc_module_name /* unused */)\n");
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
                    puts("    , ");
                    putns(varp, protName + "{vlSymsp->TOP." + protName + "}\n");
                }
            }
        }

        // Setup cell pointers
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCell* const cellp = VN_CAST(nodep, Cell)) {
                const string protName = cellp->nameProtect();
                puts("    , ");
                putns(cellp, protName + "{vlSymsp->TOP." + protName + "}\n");
            }
        }

        // Setup rootp root instance pointer,
        puts("    , rootp{&(vlSymsp->TOP)}\n");

        puts("{\n");
        puts("// Register model with the context\n");
        puts("contextp()->addModel(this);\n");
        if (v3Global.opt.trace())
            puts("contextp()->traceBaseModelCbAdd(\n"
                 "[this](VerilatedTraceBaseC* tfp, int levels, int options) {"
                 " traceBaseModel(tfp, levels, options); });\n");

        if (optSystemC()) {
            // Create sensitivity list for when to evaluate the model.
            putsDecoration(nullptr, "// Sensitivities on all clocks and combinational inputs\n");
            puts("SC_METHOD(eval);\n");
            if (v3Global.usesTiming()) puts("SC_METHOD(eval_sens);\n");
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
                            const string ivar = "__Vi"s + cvtToStr(vecnum);
                            putns(varp, "for (int __Vi" + cvtToStr(vecnum) + " = "
                                            + cvtToStr(arrayp->lo()));
                            puts("; " + ivar + " <= " + cvtToStr(arrayp->hi()));
                            puts("; ++" + ivar + ") {\n");
                        }
                        putns(varp, "sensitive << " + varp->nameProtect());
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

    void emitStandardMethods1(AstNodeModule* modp) {
        UASSERT_OBJ(modp->isTop(), modp, "Attempting to emitWrapEval for non-top class");

        const string topModNameProtected = prefixNameProtect(modp);
        const string selfDecl = "(" + topModNameProtected + "* vlSelf)";

        putSectionDelimiter("Evaluation function");

        // Forward declarations
        puts("\n");
        puts("#ifdef VL_DEBUG\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_debug_assertions") + selfDecl
             + ";\n");
        puts("#endif  // VL_DEBUG\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_static") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_initial") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval_settle") + selfDecl + ";\n");
        puts("void " + topModNameProtected + "__" + protect("_eval") + selfDecl + ";\n");

        if (optSystemC() && v3Global.usesTiming()) {
            // ::eval
            puts("\nvoid " + topClassName() + "::eval() {\n");
            puts("eval_step();\n");
            puts("if (eventsPending()) {\n");
            puts("sc_core::sc_time dt = sc_core::sc_time::from_value(nextTimeSlot() - "
                 "contextp()->time());\n");
            puts("next_trigger(dt, trigger_eval);\n");
            puts("} else {\n");
            puts("next_trigger(trigger_eval);\n");
            puts("}\n");
            puts("}\n");

            // ::eval_sens
            puts("\nvoid " + topClassName() + "::eval_sens() {\n");
            puts("trigger_eval.notify();\n");
            puts("}\n");
        }

        // ::eval_step
        puts("\nvoid " + topClassName() + "::eval_step() {\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+++++TOP Evaluate " + topClassName()
             + "::eval_step\\n\"); );\n");

        puts("#ifdef VL_DEBUG\n");
        putsDecoration(nullptr, "// Debug assertions\n");
        puts(topModNameProtected + "__" + protect("_eval_debug_assertions")
             + "(&(vlSymsp->TOP));\n");
        puts("#endif  // VL_DEBUG\n");

        if (v3Global.opt.trace()) puts("vlSymsp->__Vm_activity = true;\n");

        if (v3Global.hasEvents()) puts("vlSymsp->clearTriggeredEvents();\n");
        if (v3Global.hasClasses()) puts("vlSymsp->__Vm_deleter.deleteAll();\n");

        puts("if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {\n");
        puts("vlSymsp->__Vm_didInit = true;\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+ Initial\\n\"););\n");
        puts(topModNameProtected + "__" + protect("_eval_static") + "(&(vlSymsp->TOP));\n");
        puts(topModNameProtected + "__" + protect("_eval_initial") + "(&(vlSymsp->TOP));\n");
        puts(topModNameProtected + "__" + protect("_eval_settle") + "(&(vlSymsp->TOP));\n");
        puts("}\n");

        if (v3Global.opt.profExec()) puts("vlSymsp->__Vm_executionProfilerp->configure();\n");

        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+ Eval\\n\"););\n");
        puts(topModNameProtected + "__" + protect("_eval") + "(&(vlSymsp->TOP));\n");

        putsDecoration(nullptr, "// Evaluate cleanup\n");
        puts("Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);\n");

        puts("}\n");
    }

    void emitStandardMethods2(AstNodeModule* modp) {
        const string topModNameProtected = prefixNameProtect(modp);
        const string selfDecl = "(" + topModNameProtected + "* vlSelf)";

        // ::eval_end_step
        if (v3Global.needTraceDumper() && !optSystemC()) {
            puts("\n");
            putns(modp, "void " + topClassName() + "::eval_end_step() {\n");
            puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+eval_end_step " + topClassName()
                 + "::eval_end_step\\n\"); );\n");
            puts("#ifdef VM_TRACE\n");
            putsDecoration(nullptr, "// Tracing\n");
            // SystemC's eval loop deals with calling trace, not us
            puts("if (VL_UNLIKELY(vlSymsp->__Vm_dumping)) vlSymsp->_traceDump();\n");
            puts("#endif  // VM_TRACE\n");
            puts("}\n");
        }

        putSectionDelimiter("Events and timing");
        if (auto* const delaySchedp = v3Global.rootp()->delaySchedulerp()) {
            putns(modp, "bool " + topClassName() + "::eventsPending() { return !vlSymsp->TOP.");
            puts(delaySchedp->nameProtect());
            puts(".empty(); }\n\n");

            putns(modp, "uint64_t " + topClassName() + "::nextTimeSlot() { return vlSymsp->TOP.");
            puts(delaySchedp->nameProtect());
            puts(".nextTimeSlot(); }\n");
        } else {
            putns(modp, "bool " + topClassName() + "::eventsPending() { return false; }\n\n");
            puts("uint64_t " + topClassName() + "::nextTimeSlot() {\n");
            puts("VL_FATAL_MT(__FILE__, __LINE__, \"\", \"%Error: No delays in the "
                 "design\");\n");
            puts("return 0;\n}\n");
        }

        putSectionDelimiter("Utilities");

        if (!optSystemC()) {
            // ::name
            puts("\n");
            putns(modp, "const char* " + topClassName() + "::name() const {\n");
            puts(/**/ "return vlSymsp->name();\n");
            puts("}\n");
        }

        putSectionDelimiter("Invoke final blocks");
        // Forward declarations
        puts("\n");
        putns(modp,
              "void " + topModNameProtected + "__" + protect("_eval_final") + selfDecl + ";\n");
        // ::final
        puts("\nVL_ATTR_COLD void " + topClassName() + "::final() {\n");
        puts(/**/ topModNameProtected + "__" + protect("_eval_final") + "(&(vlSymsp->TOP));\n");
        puts("}\n");

        putSectionDelimiter("Implementations of abstract methods from VerilatedModel\n");
        putns(modp, "const char* " + topClassName()
                        + "::hierName() const { return vlSymsp->name(); }\n");
        putns(modp, "const char* " + topClassName() + "::modelName() const { return \""
                        + topClassName() + "\"; }\n");
        putns(modp, "unsigned " + topClassName() + "::threads() const { return "
                        + cvtToStr(v3Global.opt.threads()) + "; }\n");
        putns(modp, "void " + topClassName()
                        + "::prepareClone() const { contextp()->prepareClone(); }\n");
        putns(modp, "void " + topClassName() + "::atClone() const {\n");
        if (v3Global.opt.threads() > 1) {
            puts("vlSymsp->__Vm_threadPoolp = static_cast<VlThreadPool*>(");
        }
        puts("contextp()->threadPoolpOnClone()");
        if (v3Global.opt.threads() > 1) puts(")");
        puts(";\n}\n");

        if (v3Global.opt.trace()) {
            putns(modp, "std::unique_ptr<VerilatedTraceConfig> " + topClassName()
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
        putns(modp, "\nvoid " + topModNameProtected + "__" + protect("trace_decl_types") + "("
                        + v3Global.opt.traceClassBase() + "* tracep);\n");
        putns(modp, "\nvoid " + topModNameProtected + "__" + protect("trace_init_top") + "("
                        + topModNameProtected + "* vlSelf, " + v3Global.opt.traceClassBase()
                        + "* tracep);\n");

        // Static helper function
        puts("\n");
        putns(modp, "VL_ATTR_COLD static void " + protect("trace_init") + "(void* voidSelf, "
                        + v3Global.opt.traceClassBase() + "* tracep, uint32_t code) {\n");
        putsDecoration(modp, "// Callback from tracep->open()\n");
        puts(voidSelfAssign(modp));
        puts(symClassAssign());
        puts("if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {\n");
        puts("VL_FATAL_MT(__FILE__, __LINE__, __FILE__,\n");
        puts("\"Turning on wave traces requires Verilated::traceEverOn(true) call before time "
             "0.\");\n");
        puts("}\n");
        puts("vlSymsp->__Vm_baseCode = code;\n");
        puts("tracep->pushPrefix(std::string{vlSymsp->name()}, "
             "VerilatedTracePrefixType::SCOPE_MODULE);\n");
        puts(topModNameProtected + "__" + protect("trace_decl_types") + "(tracep);\n");
        puts(topModNameProtected + "__" + protect("trace_init_top") + "(vlSelf, tracep);\n");
        puts("tracep->popPrefix();\n");
        puts("}\n");

        // Forward declaration
        puts("\n");
        putns(modp, "VL_ATTR_COLD void " + topModNameProtected + "__" + protect("trace_register")
                        + "(" + topModNameProtected + "* vlSelf, " + v3Global.opt.traceClassBase()
                        + "* tracep);\n");

        // ::traceRegisterModel
        puts("\n");
        putns(modp, "VL_ATTR_COLD void " + topClassName() + "::traceBaseModel(");
        puts("VerilatedTraceBaseC* tfp, int levels, int options) {\n");
        if (optSystemC()) {
            puts(/**/ "if (!sc_core::sc_get_curr_simcontext()->elaboration_done()) {\n");
            puts(/****/ "vl_fatal(__FILE__, __LINE__, name(), \"" + topClassName()
                 + +"::trace() is called before sc_core::sc_start(). "
                    "Run sc_core::sc_start(sc_core::SC_ZERO_TIME) before trace() to complete "
                    "elaboration.\");\n");
            puts(/**/ "}");
        }
        puts(/**/ "(void)levels; (void)options;\n");  // Prevent unused variable warning
        puts(/**/ v3Global.opt.traceClassBase() + "C* const stfp = dynamic_cast<"
             + v3Global.opt.traceClassBase() + "C*>(tfp);\n");
        puts(/**/ "if (VL_UNLIKELY(!stfp)) {\n");
        puts(/****/ "vl_fatal(__FILE__, __LINE__, __FILE__,\"'" + topClassName()
             + "::trace()' called on non-" + v3Global.opt.traceClassBase() + "C object;\"\n"
             + "\" use --trace-fst with VerilatedFst object,"
             + " and --trace with VerilatedVcd object\");\n");
        puts(/**/ "}\n");
        puts(/**/ "stfp->spTrace()->addModel(this);\n");
        puts(/**/ "stfp->spTrace()->addInitCb(&" + protect("trace_init")
             + ", &(vlSymsp->TOP));\n");
        puts(/**/ topModNameProtected + "__" + protect("trace_register")
             + "(&(vlSymsp->TOP), stfp->spTrace());\n");
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
        m_ofp = v3Global.opt.systemC() ? new V3OutScFile{filename} : new V3OutCFile{filename};

        ofp()->putsHeader();
        puts("// DESCRIPTION: Verilator output: "
             "Model implementation (design independent parts)\n");

        puts("\n");
        puts("#include \"" + pchClassName() + ".h\"\n");
        if (v3Global.opt.trace()) {
            puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
        }

        emitConstructorImplementation(modp);
        emitDestructorImplementation();
        emitStandardMethods1(modp);
        emitStandardMethods2(modp);
        if (v3Global.opt.trace()) emitTraceMethods(modp);
        if (v3Global.opt.savable()) emitSerializationFunctions();

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

            iterateConst(funcp);
        }

        if (m_ofp) VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }

    void main(AstNodeModule* modp) {
        m_modp = modp;
        emitHeader(modp);
        emitImplementation(modp);
        if (v3Global.dpi()) emitDpiExportDispatchers(modp);
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
