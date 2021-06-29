// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include <vector>
#include <unordered_set>

//###################################################################### >
// Internal EmitC implementation

class EmitCImp final : EmitCFunc {
    // MEMBERS
    AstNodeModule* m_fileModp = nullptr;  // Files (names, headers) constructed using this module
    bool m_slow = false;  // Creating __Slow file
    bool m_fast = false;  // Creating non __Slow file (or both)

    //---------------------------------------
    // METHODS

    V3OutCFile* newOutCFile(bool slow, bool source, int filenum = 0) {
        m_lazyDecls.reset();  // Need to emit new lazy declarations

        string filenameNoExt = v3Global.opt.makeDir() + "/" + prefixNameProtect(m_fileModp);
        if (filenum) filenameNoExt += "__" + cvtToStr(filenum);
        filenameNoExt += (slow ? "__Slow" : "");
        V3OutCFile* ofp = nullptr;
        if (v3Global.opt.lintOnly()) {
            // Unfortunately we have some lint checks here, so we can't just skip processing.
            // We should move them to a different stage.
            const string filename = VL_DEV_NULL;
            newCFile(filename, slow, source);
            ofp = new V3OutCFile(filename);
        } else if (optSystemC()) {
            const string filename = filenameNoExt + (source ? ".cpp" : ".h");
            newCFile(filename, slow, source);
            ofp = new V3OutScFile(filename);
        } else {
            const string filename = filenameNoExt + (source ? ".cpp" : ".h");
            newCFile(filename, slow, source);
            ofp = new V3OutCFile(filename);
        }

        ofp->putsHeader();
        if (m_fileModp->isTop() && !source) {
            ofp->puts("// DESCR"
                      "IPTION: Verilator output: Primary design header\n");
            ofp->puts("//\n");
            ofp->puts("// This header should be included by all source files instantiating the "
                      "design.\n");
            ofp->puts("// The class here is then constructed to instantiate the design.\n");
            ofp->puts("// See the Verilator manual for examples.\n");
        } else {
            if (source) {
                ofp->puts("// DESCR"
                          "IPTION: Verilator output: Design implementation internals\n");
            } else {
                ofp->puts("// DESCR"
                          "IPTION: Verilator output: Design internal header\n");
            }
            ofp->puts("// See " + v3Global.opt.prefix() + ".h for the primary calling header\n");
        }
        return ofp;
    }

    //---------------------------------------
    // VISITORS
    using EmitCFunc::visit;  // Suppress hidden overloaded virtual function warning
    virtual void visit(AstCFunc* nodep) override {
        // TRACE_* and DPI handled elsewhere
        if (nodep->funcType().isTrace()) return;
        if (nodep->dpiImportPrototype()) return;
        if (!(nodep->slow() ? m_slow : m_fast)) return;

        maybeSplit();

        EmitCFunc::visit(nodep);
    }

    //---------------------------------------
    // ACCESSORS

    // METHODS
    // Low level
    void emitTypedefs(AstNode* firstp) {
        bool first = true;
        for (AstNode* loopp = firstp; loopp; loopp = loopp->nextp()) {
            if (const AstTypedef* nodep = VN_CAST(loopp, Typedef)) {
                if (nodep->attrPublic()) {
                    if (first) {
                        first = false;
                        puts("\n// TYPEDEFS\n");
                        puts("// That were declared public\n");
                    } else {
                        puts("\n");
                    }
                    if (const AstEnumDType* adtypep
                        = VN_CAST(nodep->dtypep()->skipRefToEnump(), EnumDType)) {
                        if (adtypep->width() > 64) {
                            putsDecoration("// enum " + nodep->nameProtect()
                                           + " // Ignored: Too wide for C++\n");
                        } else {
                            puts("enum " + nodep->name() + " {\n");
                            for (AstEnumItem* itemp = adtypep->itemsp(); itemp;
                                 itemp = VN_CAST(itemp->nextp(), EnumItem)) {
                                puts(itemp->nameProtect());
                                puts(" = ");
                                iterateAndNextNull(itemp->valuep());
                                if (VN_IS(itemp->nextp(), EnumItem)) puts(",");
                                puts("\n");
                            }
                            puts("};\n");
                        }
                    }
                }
            }
        }
    }
    void emitParams(AstNodeModule* modp, bool init, bool* firstp, string& sectionr) {
        bool anyi = false;
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* varp = VN_CAST(nodep, Var)) {
                if (varp->isParam() && (varp->isUsedParam() || varp->isSigPublic())) {
                    if (!init && sectionr != "") {
                        puts(sectionr);
                        sectionr = "";
                    }
                    UASSERT_OBJ(varp->valuep(), nodep, "No init for a param?");
                    // These should be static const values, however older MSVC++ did't
                    // support them; should be ok now under C++11, need to refactor.
                    if (varp->isWide()) {  // Unsupported for output
                        if (!init) {
                            putsDecoration("// enum WData " + varp->nameProtect() + "  //wide");
                        }
                    } else if (varp->isString()) {
                        if (init) {
                            puts("const std::string ");
                            puts(prefixNameProtect(modp) + "::" + protect("var_" + varp->name())
                                 + "(");
                            iterateAndNextNull(varp->valuep());
                            puts(");\n");
                            anyi = true;
                        } else {
                            puts("static const std::string " + protect("var_" + varp->name())
                                 + ";\n");
                        }
                    } else if (!VN_IS(varp->valuep(), Const)) {  // Unsupported for output
                        // putsDecoration("// enum ..... "+varp->nameProtect()
                        //               +"not simple value, see variable above instead");
                    } else if (VN_IS(varp->dtypep(), BasicDType)
                               && VN_CAST(varp->dtypep(), BasicDType)
                                      ->isOpaque()) {  // Can't put out e.g. doubles
                    } else {
                        if (init) {
                            puts(varp->isQuad() ? "const QData " : "const IData ");
                            puts(prefixNameProtect(modp) + "::" + protect("var_" + varp->name())
                                 + "(");
                            iterateAndNextNull(varp->valuep());
                            puts(");\n");
                            anyi = true;
                        } else {
                            // enum
                            puts(varp->isQuad() ? "enum _QData" : "enum _IData");
                            puts("" + varp->nameProtect() + " { " + varp->nameProtect() + " = ");
                            iterateAndNextNull(varp->valuep());
                            puts("};\n");
                            // var
                            puts(varp->isQuad() ? "static const QData " : "static const IData ");
                            puts(protect("var_" + varp->name()) + ";\n");
                        }
                    }
                }
            }
        }
        if (anyi) puts("\n");
    }
    void emitSensitives();
    // Medium level
    void emitCtorImp(AstNodeModule* modp);
    void emitConfigureImp(AstNodeModule* modp);
    void emitCoverageDecl(AstNodeModule* modp);
    void emitCoverageImp(AstNodeModule* modp);
    void emitDestructorImp(AstNodeModule* modp);
    void emitSavableImp(AstNodeModule* modp);
    void emitTextSection(AstType type);
    // High level
    void emitImpTop();
    void emitImp(AstNodeModule* modp);
    void emitSettleLoop(bool initial);
    void emitWrapEval();
    void emitWrapFast();
    void emitThreadingState();
    void emitThreadingCtors(bool* firstp);
    void emitIntTop(const AstNodeModule* modp);
    void emitInt(AstNodeModule* modp);
    void maybeSplit();

public:
    EmitCImp() {}
    virtual ~EmitCImp() override = default;
    void mainImp(AstNodeModule* modp, bool slow);
    void mainInt(AstNodeModule* modp);
    void mainDoFunc(AstCFunc* nodep) { iterate(nodep); }
};

//######################################################################
// Internal EmitC

void EmitCImp::emitCoverageDecl(AstNodeModule*) {
    if (v3Global.opt.coverage()) {
        ofp()->putsPrivate(false);  // Accessed from loose methods
        putsDecoration("// Coverage\n");
        puts("void __vlCoverInsert(");
        puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
        puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
        puts("const char* hierp, const char* pagep, const char* commentp, const char* "
             "linescovp);\n");
    }
}

void EmitCImp::emitThreadingCtors(bool* firstp) {
    ofp()->indentInc();
    emitCtorSep(firstp);
    puts("__Vm_threadPoolp(nullptr)");
    emitCtorSep(firstp);
    puts("__Vm_even_cycle(false)");
    if (v3Global.opt.profThreads()) {
        emitCtorSep(firstp);
        puts("__Vm_profile_cycle_start(0)");
    }
    ofp()->indentDec();
}

void EmitCImp::emitCtorImp(AstNodeModule* modp) {
    puts("\n");
    bool first = true;
    string section;
    emitParams(modp, true, &first, section /*ref*/);

    const string modName = prefixNameProtect(modp);

    puts("\n");
    m_lazyDecls.emit("void " + modName + "__", protect("_ctor_var_reset"),
                     "(" + modName + "* vlSelf);");
    puts("\n");

    if (VN_IS(modp, Class)) {
        modp->v3fatalSrc("constructors should be AstCFuncs instead");
    } else if (optSystemC() && modp->isTop()) {
        puts(modName + "::" + modName + "(sc_module_name)");
    } else if (modp->isTop()) {
        puts(modName + "::" + modName
             + "(VerilatedContext* _vcontextp__, const char* _vcname__)\n");
        puts("    : VerilatedModule{_vcname__}\n");
        first = false;  // printed the first ':'
    } else {
        puts(modName + "::" + modName + "(const char* _vcname__)\n");
        puts("    : VerilatedModule(_vcname__)\n");
        first = false;  // printed the first ':'
    }
    emitVarCtors(&first);
    if (modp->isTop() && v3Global.opt.mtasks()) emitThreadingCtors(&first);

    puts(" {\n");

    if (modp->isTop()) {
        putsDecoration("// Create Sym instance\n");
        // Must be before other constructors, as __vlCoverInsert calls it.
        // Note _vcontextp__ may be nullptr, VerilatedSyms::VerilatedSyms cleans it up
        puts(EmitCBaseVisitor::symClassVar() + " = new " + symClassName() + "("
             + (optSystemC() ? "nullptr" : "_vcontextp__") + ", this, name());\n");
    }

    emitSensitives();

    putsDecoration("// Reset structure values\n");
    puts(modName + "__" + protect("_ctor_var_reset") + "(this);\n");
    emitTextSection(AstType::atScCtor);

    if (modp->isTop() && v3Global.opt.mtasks()) {
        // TODO-- For now each top module creates its own ThreadPool here,
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
        puts("__Vm_threadPoolp = new VlThreadPool("
             // Note we create N-1 threads in the thread pool. The thread
             // that calls eval() becomes the final Nth thread for the
             // duration of the eval call.
             + string("vlSymsp->_vm_contextp__, ") + cvtToStr(v3Global.opt.threads() - 1) + ", "
             + cvtToStr(v3Global.opt.profThreads()) + ");\n");
    }
    puts("}\n");
}

void EmitCImp::emitConfigureImp(AstNodeModule* modp) {
    const string modName = prefixNameProtect(modp);

    if (v3Global.opt.coverage()) {
        puts("\n");
        m_lazyDecls.emit("void " + modName + "__", protect("_configure_coverage"),
                         "(" + modName + "* vlSelf, bool first);");
    }

    puts("\nvoid " + modName + "::" + protect("__Vconfigure") + "(" + symClassName()
         + "* _vlSymsp, bool first) {\n");
    puts("if (false && first) {}  // Prevent unused\n");
    puts("this->vlSymsp = _vlSymsp;\n");  // First, as later stuff needs it.
    if (v3Global.opt.coverage()) {
        puts(modName + "__" + protect("_configure_coverage") + "(this, first);\n");
    }
    puts("}\n");
    splitSizeInc(10);
}

void EmitCImp::emitCoverageImp(AstNodeModule*) {
    if (v3Global.opt.coverage()) {
        puts("\n// Coverage\n");
        // Rather than putting out VL_COVER_INSERT calls directly, we do it via this function
        // This gets around gcc slowness constructing all of the template arguments.
        puts("void " + prefixNameProtect(m_modp) + "::__vlCoverInsert(");
        puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
        puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
        puts("const char* hierp, const char* pagep, const char* commentp, const char* linescovp) "
             "{\n");
        if (v3Global.opt.threads()) {
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
        // puts( "\"hier\",std::string(vlSymsp->name())+hierp,");
        puts("\"hier\",std::string(name())+hierp,");
        puts("  \"page\",pagep,");
        puts("  \"comment\",commentp,");
        puts("  (linescovp[0] ? \"linescov\" : \"\"), linescovp);\n");
        puts("}\n");
        splitSizeInc(10);
    }
}

void EmitCImp::emitDestructorImp(AstNodeModule* modp) {
    puts("\n");
    puts(prefixNameProtect(modp) + "::~" + prefixNameProtect(modp) + "() {\n");
    if (modp->isTop()) {
        if (v3Global.opt.mtasks()) {
            puts("VL_DO_CLEAR(delete __Vm_threadPoolp, __Vm_threadPoolp = nullptr);\n");
        }
        // Call via function in __Trace.cpp as this .cpp file does not have trace header
        if (v3Global.needTraceDumper()) {
            puts("#ifdef VM_TRACE\n");
            puts("if (VL_UNLIKELY(vlSymsp->__Vm_dumping)) _traceDumpClose();\n");
            puts("#endif  // VM_TRACE\n");
        }
    }
    emitTextSection(AstType::atScDtor);
    if (modp->isTop()) puts("VL_DO_CLEAR(delete vlSymsp, vlSymsp = nullptr);\n");
    puts("}\n");
    splitSizeInc(10);
}

void EmitCImp::emitSavableImp(AstNodeModule* modp) {
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
                if (const AstVar* varp = VN_CAST(nodep, Var)) {
                    hash.insert(varp->name());
                    hash.insert(varp->dtypep()->width());
                }
            }
            ofp()->printf("vluint64_t __Vcheckval = 0x%" VL_PRI64 "xULL;\n",
                          static_cast<vluint64_t>(hash.digestUInt64()));
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
                if (const AstVar* varp = VN_CAST(nodep, Var)) {
                    if (varp->isIO() && modp->isTop() && optSystemC()) {
                        // System C top I/O doesn't need loading, as the
                        // lower level subinst code does it.
                    } else if (varp->isParam()) {
                    } else if (varp->isStatic() && varp->isConst()) {
                    } else {
                        int vects = 0;
                        AstNodeDType* elementp = varp->dtypeSkipRefp();
                        for (AstUnpackArrayDType* arrayp = VN_CAST(elementp, UnpackArrayDType);
                             arrayp; arrayp = VN_CAST(elementp, UnpackArrayDType)) {
                            const int vecnum = vects++;
                            UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                        "Should have swapped msb & lsb earlier.");
                            const string ivar = string("__Vi") + cvtToStr(vecnum);
                            puts("for (int __Vi" + cvtToStr(vecnum) + "=" + cvtToStr(0));
                            puts("; " + ivar + "<" + cvtToStr(arrayp->elementsConst()));
                            puts("; ++" + ivar + ") {\n");
                            elementp = arrayp->subDTypep()->skipRefp();
                        }
                        const AstBasicDType* const basicp = elementp->basicp();
                        // Do not save MTask state, only matters within an evaluation
                        if (basicp && basicp->keyword().isMTaskState()) continue;
                        // Want to detect types that are represented as arrays
                        // (i.e. packed types of more than 64 bits).
                        if (elementp->isWide()
                            && !(basicp && basicp->keyword() == AstBasicDTypeKwd::STRING)) {
                            const int vecnum = vects++;
                            const string ivar = string("__Vi") + cvtToStr(vecnum);
                            puts("for (int __Vi" + cvtToStr(vecnum) + "=" + cvtToStr(0));
                            puts("; " + ivar + "<" + cvtToStr(elementp->widthWords()));
                            puts("; ++" + ivar + ") {\n");
                        }
                        puts("os" + op + varp->nameProtect());
                        for (int v = 0; v < vects; ++v) puts("[__Vi" + cvtToStr(v) + "]");
                        puts(";\n");
                        for (int v = 0; v < vects; ++v) puts("}\n");
                    }
                }
            }

            if (modp->isTop()) {  // Save the children
                puts("vlSymsp->" + protect(funcname) + "(os);\n");
            }
            puts("}\n");
        }
    }
}

void EmitCImp::emitTextSection(AstType type) {
    int last_line = -999;
    for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (const AstNodeText* textp = VN_CAST(nodep, NodeText)) {
            if (nodep->type() == type) {
                if (last_line != nodep->fileline()->lineno()) {
                    if (last_line < 0) {
                        puts("\n//*** Below code from `systemc in Verilog file\n");
                    }
                    putsDecoration(
                        ifNoProtect("// From `systemc at " + nodep->fileline()->ascii() + "\n"));
                    last_line = nodep->fileline()->lineno();
                }
                ofp()->putsNoTracking(textp->text());
                last_line++;
            }
        }
    }
    if (last_line > 0) puts("//*** Above code from `systemc in Verilog file\n\n");
}

void EmitCImp::emitSensitives() {
    // Create sensitivity list for when to evaluate the model.
    // If C++ code, the user must call this routine themself.
    if (m_modp->isTop() && optSystemC()) {
        putsDecoration("// Sensitivities on all clocks and combo inputs\n");
        puts("SC_METHOD(eval);\n");
        for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* varp = VN_CAST(nodep, Var)) {
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
                        puts("for (int __Vi" + cvtToStr(vecnum) + "=" + cvtToStr(arrayp->lo()));
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
}

void EmitCImp::emitSettleLoop(bool initial) {
    const string self = initial ? "vlSelf" : "this";
    putsDecoration("// Evaluate till stable\n");
    puts("int __VclockLoop = 0;\n");
    puts("QData __Vchange = 1;\n");
    if (v3Global.opt.trace()) puts("vlSymsp->__Vm_activity = true;\n");
    puts("do {\n");
    puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+ ");
    puts(initial ? "Initial" : "Clock");
    puts(" loop\\n\"););\n");
    if (initial) puts(topClassName() + "__" + protect("_eval_settle") + "(" + self + ");\n");
    puts(topClassName() + "__" + protect("_eval") + "(" + self + ");\n");
    puts("if (VL_UNLIKELY(++__VclockLoop > " + cvtToStr(v3Global.opt.convergeLimit()) + ")) {\n");
    puts("// About to fail, so enable debug to see what's not settling.\n");
    puts("// Note you must run make with OPT=-DVL_DEBUG for debug prints.\n");
    puts("int __Vsaved_debug = Verilated::debug();\n");
    puts("Verilated::debug(1);\n");
    puts("__Vchange = " + topClassName() + "__" + protect("_change_request") + "(" + self
         + ");\n");
    puts("Verilated::debug(__Vsaved_debug);\n");
    puts("VL_FATAL_MT(");
    putsQuoted(protect(m_modp->fileline()->filename()));
    puts(", ");
    puts(cvtToStr(m_modp->fileline()->lineno()));
    puts(", \"\",\n");
    puts("\"Verilated model didn't ");
    if (initial) puts("DC ");
    puts("converge\\n\"\n");
    puts("\"- See https://verilator.org/warn/DIDNOTCONVERGE\");\n");
    puts("} else {\n");
    puts("__Vchange = " + topClassName() + "__" + protect("_change_request") + "(" + self
         + ");\n");
    puts("}\n");
    puts("} while (VL_UNLIKELY(__Vchange));\n");
}

void EmitCImp::emitWrapFast() {
    UASSERT_OBJ(m_modp->isTop(), m_modp, "Attempting to emitWrapFast for non-top class");
    puts("\nVerilatedContext* " + topClassName() + "::contextp() const {\n");
    puts(/**/ "return vlSymsp->_vm_contextp__;\n");
    puts("}\n");
}

void EmitCImp::emitWrapEval() {
    UASSERT_OBJ(m_modp->isTop(), m_modp, "Attempting to emitWrapEval for non-top class");

    const string selfDecl = "(" + topClassName() + "* vlSelf)";

    // Forward declarations
    puts("\n");
    m_lazyDecls.emit("void " + topClassName() + "__", protect("_eval_initial"), selfDecl + ";");
    m_lazyDecls.emit("void " + topClassName() + "__", protect("_eval_settle"), selfDecl + ";");
    m_lazyDecls.emit("void " + topClassName() + "__", protect("_eval"), selfDecl + ";");
    m_lazyDecls.emit("QData " + topClassName() + "__", protect("_change_request"), selfDecl + ";");
    puts("#ifdef VL_DEBUG\n");
    m_lazyDecls.emit("void " + topClassName() + "__", protect("_eval_debug_assertions"),
                     selfDecl + ";");
    puts("#endif  // VL_DEBUG\n");
    m_lazyDecls.emit("void " + topClassName() + "__", protect("_final"), selfDecl + ";");

    // _eval_initial_loop
    puts("\nstatic void " + protect("_eval_initial_loop") + selfDecl + " {\n");
    puts(symClassAssign());
    puts("vlSymsp->__Vm_didInit = true;\n");
    puts(topClassName() + "__" + protect("_eval_initial") + "(vlSelf);\n");
    emitSettleLoop(/* initial: */ true);
    ensureNewLine();
    puts("}\n");

    // ::eval_step
    puts("\nvoid " + topClassName() + "::eval_step() {\n");
    puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+++++TOP Evaluate " + topClassName()
         + "::eval_step\\n\"); );\n");
    puts("#ifdef VL_DEBUG\n");
    putsDecoration("// Debug assertions\n");
    puts(topClassName() + "__" + protect("_eval_debug_assertions") + "(this);\n");
    puts("#endif  // VL_DEBUG\n");
    putsDecoration("// Initialize\n");
    puts("if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) " + protect("_eval_initial_loop")
         + "(this);\n");

    if (v3Global.opt.threads() == 1) {
        uint32_t mtaskId = 0;
        putsDecoration("// MTask " + cvtToStr(mtaskId) + " start\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"MTask" + cvtToStr(mtaskId) + " starting\\n\"););\n");
        puts("Verilated::mtaskId(" + cvtToStr(mtaskId) + ");\n");
    }

    if (v3Global.opt.mtasks() && v3Global.opt.profThreads()) {
        puts("if (VL_UNLIKELY((vlSymsp->_vm_contextp__->profThreadsStart() != "
             "__Vm_profile_time_finished)\n");
        puts(" && (VL_TIME_Q() > vlSymsp->_vm_contextp__->profThreadsStart())\n");
        puts(" && (vlSymsp->_vm_contextp__->profThreadsWindow() >= 1))) {\n");
        // Within a profile (either starting, middle, or end)
        puts("if (__Vm_profile_window_ct == 0) {\n");  // Opening file?
        // Start profile on this cycle. We'll capture a window worth, then
        // only analyze the next window worth. The idea is that the first window
        // capture will hit some cache-cold stuff (eg printf) but it'll be warm
        // by the time we hit the second window, we hope.
        puts("__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
        // "* 2" as first half is warmup, second half is collection
        puts("__Vm_profile_window_ct = vlSymsp->_vm_contextp__->profThreadsWindow() * 2 "
             "+ "
             "1;\n");
        puts("}\n");
        puts("--__Vm_profile_window_ct;\n");
        puts("if (__Vm_profile_window_ct == vlSymsp->_vm_contextp__->profThreadsWindow()) "
             "{\n");
        // This barrier record in every threads' profile demarcates the
        // cache-warm-up cycles before the barrier from the actual profile
        // cycles afterward.
        puts("__Vm_threadPoolp->profileAppendAll(");
        puts("VlProfileRec(VlProfileRec::Barrier()));\n");
        puts("__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
        puts("}\n");
        puts("else if (__Vm_profile_window_ct == 0) {\n");
        // Ending file.
        puts("vluint64_t elapsed = VL_RDTSC_Q() - __Vm_profile_cycle_start;\n");
        puts("__Vm_threadPoolp->profileDump(vlSymsp->_vm_contextp__->profThreadsFilename()."
             "c_str(), elapsed);\n");
        // This turns off the test to enter the profiling code, but still
        // allows the user to collect another profile by changing
        // profThreadsStart
        puts("__Vm_profile_time_finished = vlSymsp->_vm_contextp__->profThreadsStart();\n");
        puts("__Vm_profile_cycle_start = 0;\n");
        puts("}\n");
        puts("}\n");
    }

    emitSettleLoop(/* initial: */ false);
    if (v3Global.opt.threads() == 1) {
        puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");
    }
    if (v3Global.opt.threads()) puts("Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);\n");
    puts("}\n");
    splitSizeInc(10);

    // ::eval_end_step
    if (v3Global.needTraceDumper() && !optSystemC()) {
        puts("\nvoid " + topClassName() + "::eval_end_step() {\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+eval_end_step " + topClassName()
             + "::eval_end_step\\n\"); );\n");
        puts("#ifdef VM_TRACE\n");
        putsDecoration("// Tracing\n");
        // SystemC's eval loop deals with calling trace, not us
        puts("if (VL_UNLIKELY(vlSymsp->__Vm_dumping)) _traceDump();\n");
        puts("#endif  // VM_TRACE\n");
        puts("}\n");
        splitSizeInc(10);
    }

    // ::final
    puts("\nvoid " + topClassName() + "::final() {\n");
    puts(topClassName() + "__" + protect("_final") + "(this);\n");
    puts("}\n");
    splitSizeInc(10);
}

void EmitCImp::emitThreadingState() {
    ofp()->putsPrivate(false);  // Accessed from loose function
    AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
    UASSERT_OBJ(execGraphp, v3Global.rootp(), "Root should have an execGraphp");

    puts("VlThreadPool* __Vm_threadPoolp;\n");
    puts("bool __Vm_even_cycle;\n");

    if (v3Global.opt.profThreads()) {
        // rdtsc() at current cycle start
        puts("vluint64_t __Vm_profile_cycle_start = 0;\n");
        // Time we finished analysis
        puts("vluint64_t __Vm_profile_time_finished = 0;\n");
        // Track our position in the cache warmup and actual profile window
        puts("vluint32_t __Vm_profile_window_ct = 0;\n");
    }
}

void EmitCImp::emitIntTop(const AstNodeModule* modp) {
    // Always have this first; gcc has short circuiting if #ifdef is first in a file
    ofp()->putsGuard();
    puts("\n");

    ofp()->putsIntTopInclude();
    if (v3Global.needHeavy()) {
        puts("#include \"verilated_heavy.h\"\n");
    } else {
        puts("#include \"verilated.h\"\n");
    }
    if (v3Global.opt.mtasks()) puts("#include \"verilated_threads.h\"\n");
    if (v3Global.opt.savable()) puts("#include \"verilated_save.h\"\n");
    if (v3Global.opt.coverage()) puts("#include \"verilated_cov.h\"\n");
    if (v3Global.dpi() && modp->isTop()) {
        // do this before including our main .h file so that any references to
        // types defined in svdpi.h are available
        puts("#include \"svdpi.h\"\n");
    }
}

void EmitCImp::emitInt(AstNodeModule* modp) {
    puts("\n//==========\n\n");

    if (AstClass* classp = VN_CAST(modp, Class)) {
        if (classp->extendsp())
            puts("#include \"" + prefixNameProtect(classp->extendsp()->classp()->classOrPackagep())
                 + ".h\"\n");
    }

    emitModCUse(modp, VUseType::INT_INCLUDE);

    // Declare foreign instances up front to make C++ happy
    puts("class " + symClassName() + ";\n");
    emitModCUse(modp, VUseType::INT_FWD_CLASS);

    puts("\n//----------\n\n");
    emitTextSection(AstType::atScHdr);

    if (AstClass* classp = VN_CAST(modp, Class)) {
        puts("class " + prefixNameProtect(modp));
        if (classp->extendsp())
            puts(" : public " + prefixNameProtect(classp->extendsp()->classp()));
        puts(" {\n");
    } else if (optSystemC() && modp->isTop()) {
        puts("SC_MODULE(" + prefixNameProtect(modp) + ") {\n");
    } else {
        puts("VL_MODULE(" + prefixNameProtect(modp) + ") {\n");
    }
    ofp()->resetPrivate();
    ofp()->putsPrivate(false);  // public:

    {  // Instantiated cells
        bool did = false;
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstCell* cellp = VN_CAST(nodep, Cell)) {
                if (!did) {
                    did = true;
                    putsDecoration("// CELLS\n");
                    if (modp->isTop()) {
                        puts("// Public to allow access to /*verilator_public*/ items;\n");
                        puts("// otherwise the application code can consider these internals.\n");
                    }
                }
                puts(prefixNameProtect(cellp->modp()) + "* " + cellp->nameProtect() + ";\n");
            }
        }
    }

    emitTypedefs(modp->stmtsp());

    string section;
    section = "\n// PORTS\n";
    if (modp->isTop()) {
        section += ("// The application code writes and reads these signals to\n"
                    "// propagate new values into/out from the Verilated model.\n");
    }
    emitVarList(modp->stmtsp(), EVL_CLASS_IO, "", section /*ref*/);

    section = "\n// LOCAL SIGNALS\n";
    if (modp->isTop()) section += "// Internals; generally not touched by application code\n";
    emitVarList(modp->stmtsp(), EVL_CLASS_SIG, "", section /*ref*/);

    section = "\n// LOCAL VARIABLES\n";
    if (modp->isTop()) section += "// Internals; generally not touched by application code\n";
    emitVarList(modp->stmtsp(), EVL_CLASS_TEMP, "", section /*ref*/);

    puts("\n// INTERNAL VARIABLES\n");
    if (modp->isTop()) puts("// Internals; generally not touched by application code\n");
    if (!VN_IS(modp, Class)) {  // Avoid clang unused error (& don't want in every object)
        ofp()->putsPrivate(false);  // public: so loose methods can pick it up
        puts(symClassName() + "* vlSymsp;  // Symbol table\n");
    }
    ofp()->putsPrivate(false);  // public:
    if (modp->isTop()) {
        if (v3Global.opt.mtasks()) emitThreadingState();
    }
    emitCoverageDecl(modp);  // may flip public/private

    section = "\n// PARAMETERS\n";
    if (modp->isTop())
        section += "// Parameters marked /*verilator public*/ for use by application code\n";
    ofp()->putsPrivate(false);  // public:
    emitVarList(modp->stmtsp(), EVL_CLASS_PAR, "",
                section /*ref*/);  // Only those that are non-CONST
    bool first = true;
    emitParams(modp, false, &first, section /*ref*/);

    if (!VN_IS(modp, Class)) {
        puts("\n// CONSTRUCTORS\n");
        ofp()->resetPrivate();
        // We don't need a private copy constructor, as VerilatedModule has one for us.
        ofp()->putsPrivate(true);
        puts("VL_UNCOPYABLE(" + prefixNameProtect(modp) + ");  ///< Copying not allowed\n");
    }

    if (VN_IS(modp, Class)) {
        // CFuncs with isConstructor/isDestructor used instead
    } else if (optSystemC() && modp->isTop()) {
        ofp()->putsPrivate(false);  // public:
        puts("SC_CTOR(" + prefixNameProtect(modp) + ");\n");
        puts("virtual ~" + prefixNameProtect(modp) + "();\n");
    } else if (optSystemC()) {
        ofp()->putsPrivate(false);  // public:
        puts(prefixNameProtect(modp) + "(const char* __VCname = \"\");\n");
        puts("~" + prefixNameProtect(modp) + "();\n");
    } else {
        ofp()->putsPrivate(false);  // public:
        if (modp->isTop()) {
            puts("/// Construct the model; called by application code\n");
            puts("/// If contextp is null, then the model will use the default global context\n");
            puts("/// If name is \"\", then makes a wrapper with a\n");
            puts("/// single model invisible with respect to DPI scope names.\n");
            puts(prefixNameProtect(modp) + "(VerilatedContext* contextp,"
                 + " const char* name = \"TOP\");\n");
            puts(prefixNameProtect(modp) + "(const char* name = \"TOP\")\n");
            puts("    : " + prefixNameProtect(modp) + "(nullptr, name) {}\n");
        } else {
            if (VN_IS(modp, Class)) {
                // TODO move all constructor definition to e.g. V3CUse
                puts(prefixNameProtect(modp) + "();\n");
            } else {
                puts(prefixNameProtect(modp) + "(const char* name = \"TOP\");\n");
            }
        }
        if (modp->isTop()) {
            puts("/// Destroy the model; called (often implicitly) by application code\n");
        }
        puts("~" + prefixNameProtect(modp) + "();\n");
    }

    if (v3Global.opt.trace() && modp->isTop()) {
        puts("/// Trace signals in the model; called by application code\n");
        puts("void trace(" + v3Global.opt.traceClassBase()
             + "C* tfp, int levels, int options = 0);\n");
        if (optSystemC()) {
            puts("/// SC tracing; avoid overloaded virtual function lint warning\n");
            puts("virtual void trace(sc_trace_file* tfp) const override { "
                 "::sc_core::sc_module::trace(tfp); }\n");
        }
    }

    emitTextSection(AstType::atScInt);

    if (modp->isTop()) {
        puts("\n// API METHODS\n");
        puts("/// Return current simulation context for this model.\n");
        puts("/// Used to get to e.g. simulation time via contextp()->time()\n");
        puts("VerilatedContext* contextp() const;\n");

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
        ofp()->putsPrivate(false);  // public:
        if (!optSystemC()) {
            puts("/// Simulation complete, run final blocks.  Application "
                 "must call on completion.\n");
        }
        puts("void final();\n");
    }

    puts("\n// INTERNAL METHODS\n");
    if (modp->isTop()) {
        ofp()->putsPrivate(false);  // public: as accessed by loose functions
        if (v3Global.needTraceDumper()) {
            if (!optSystemC()) puts("void _traceDump();\n");
            puts("void _traceDumpOpen();\n");
            puts("void _traceDumpClose();\n");
        }
    }

    if (!VN_IS(modp, Class)) {
        ofp()->putsPrivate(false);  // public:
        puts("void " + protect("__Vconfigure") + "(" + symClassName() + "* symsp, bool first);\n");
    }

    ofp()->putsPrivate(false);  // public:
    emitIntFuncDecls(modp, true);

    if (v3Global.opt.savable()) {
        ofp()->putsPrivate(false);  // public:
        puts("void " + protect("__Vserialize") + "(VerilatedSerialize& os);\n");
        puts("void " + protect("__Vdeserialize") + "(VerilatedDeserialize& os);\n");
    }

    puts("}");
    if (!VN_IS(modp, Class)) puts(" VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES)");
    puts(";\n");

    puts("\n//----------\n\n");
    emitIntFuncDecls(modp, false);

    // Save/restore
    if (v3Global.opt.savable() && modp->isTop()) {
        puts("\n");
        puts("inline VerilatedSerialize& operator<<(VerilatedSerialize& os, "
             + prefixNameProtect(modp) + "& rhs) {\n"  //
             + "Verilated::quiesce(); rhs." + protect("__Vserialize") + "(os); return os; }\n");
        puts("inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, "
             + prefixNameProtect(modp) + "& rhs) {\n"  //
             + "Verilated::quiesce(); rhs." + protect("__Vdeserialize") + "(os); return os; }\n");
    }
}

//----------------------------------------------------------------------

void EmitCImp::emitImpTop() {
    puts("\n");
    puts("#include \"" + prefixNameProtect(m_fileModp) + ".h\"\n");
    puts("#include \"" + symClassName() + ".h\"\n");

    if (v3Global.dpi()) {
        puts("\n");
        puts("#include \"verilated_dpi.h\"\n");
    }

    emitModCUse(m_fileModp, VUseType::IMP_INCLUDE);
    emitModCUse(m_fileModp, VUseType::IMP_FWD_CLASS);

    emitTextSection(AstType::atScImpHdr);
}

void EmitCImp::emitImp(AstNodeModule* modp) {
    puts("\n//==========\n");
    if (m_slow) {
        string section;
        emitVarList(modp->stmtsp(), EVL_CLASS_ALL, prefixNameProtect(modp), section /*ref*/);
        if (!VN_IS(modp, Class)) emitCtorImp(modp);
        if (!VN_IS(modp, Class)) emitConfigureImp(modp);
        if (!VN_IS(modp, Class)) emitDestructorImp(modp);
        emitSavableImp(modp);
        emitCoverageImp(modp);
    }

    if (m_fast) {
        emitTextSection(AstType::atScImp);
        if (modp->isTop()) {
            emitWrapFast();
            emitWrapEval();
        }
    }

    // Blocks
    for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (AstCFunc* funcp = VN_CAST(nodep, CFunc)) { mainDoFunc(funcp); }
    }
}

//######################################################################

void EmitCImp::maybeSplit() {
    if (!splitNeeded()) return;

    // Splitting file, so using parallel build.
    v3Global.useParallelBuild(true);
    // Close old file
    VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    // Open a new file
    m_ofp = newOutCFile(!m_fast, true /*source*/, splitFilenumInc());
    emitImpTop();
}

void EmitCImp::mainInt(AstNodeModule* modp) {
    m_modp = modp;
    m_fileModp = modp;
    m_slow = true;
    m_fast = true;

    UINFO(5, "  Emitting " << prefixNameProtect(modp) << endl);

    m_ofp = newOutCFile(false /*slow*/, false /*source*/);
    emitIntTop(modp);
    emitInt(modp);
    if (AstClassPackage* packagep = VN_CAST(modp, ClassPackage)) {
        // Put the non-static class implementation in same h file for speed
        m_modp = packagep->classp();
        emitInt(packagep->classp());
        m_modp = modp;
    }
    ofp()->putsEndGuard();
    VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
}

void EmitCImp::mainImp(AstNodeModule* modp, bool slow) {
    // Output a module
    m_modp = modp;
    m_fileModp = modp;
    m_slow = slow;
    m_fast = !slow;

    UINFO(5, "  Emitting " << prefixNameProtect(modp) << endl);

    m_ofp = newOutCFile(!m_fast, true /*source*/);
    emitImpTop();
    emitImp(modp);

    if (AstClassPackage* packagep = VN_CAST(modp, ClassPackage)) {
        // Put the non-static class implementation in same C++ files as
        // often optimizations are possible when both are seen by the
        // compiler together
        m_modp = packagep->classp();
        emitImp(packagep->classp());
        m_modp = modp;
    }

    VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
}

//######################################################################
// Tracing routines

class EmitCTrace final : EmitCFunc {
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user1() -> int.  Enum number
    AstUser1InUse m_inuser1;

    // MEMBERS
    AstCFunc* m_cfuncp = nullptr;  // Function we're in now
    bool m_slow;  // Making slow file
    int m_enumNum = 0;  // Enumeration number (whole netlist)
    int m_baseCode = -1;  // Code of first AstTraceInc in this function

    // METHODS
    void newOutCFile(int filenum) {
        m_lazyDecls.reset();  // Need to emit new lazy declarations

        string filename
            = (v3Global.opt.makeDir() + "/" + topClassName() + "_" + protect("_Trace"));
        if (filenum) filename += "__" + cvtToStr(filenum);
        filename += (m_slow ? "__Slow" : "");
        filename += ".cpp";

        AstCFile* cfilep = newCFile(filename, m_slow, true /*source*/);
        cfilep->support(true);

        if (m_ofp) v3fatalSrc("Previous file not closed");
        if (optSystemC()) {
            m_ofp = new V3OutScFile(filename);
        } else {
            m_ofp = new V3OutCFile(filename);
        }
        m_ofp->putsHeader();
        m_ofp->puts("// DESCR"
                    "IPTION: Verilator output: Tracing implementation internals\n");

        emitTraceHeader();
    }

    void emitTraceHeader() {
        // Includes
        puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
        puts("#include \"" + symClassName() + ".h\"\n");
        puts("\n");
    }

    void emitTraceSlow() {
        puts("\n//======================\n");

        if (v3Global.needTraceDumper() && !optSystemC()) {
            puts("\nvoid " + topClassName() + "::_traceDump() {\n");
            // Caller checked for __Vm_dumperp non-nullptr
            puts("const VerilatedLockGuard lock(vlSymsp->__Vm_dumperMutex);\n");
            puts("vlSymsp->__Vm_dumperp->dump(VL_TIME_Q());\n");
            puts("}\n");
            splitSizeInc(10);
        }

        if (v3Global.needTraceDumper()) {
            puts("\nvoid " + topClassName() + "::_traceDumpOpen() {\n");
            puts("const VerilatedLockGuard lock(vlSymsp->__Vm_dumperMutex);\n");
            puts("if (VL_UNLIKELY(!vlSymsp->__Vm_dumperp)) {\n");
            puts("vlSymsp->__Vm_dumperp = new " + v3Global.opt.traceClassLang() + "();\n");
            puts("trace(vlSymsp->__Vm_dumperp, 0, 0);\n");
            puts("std::string dumpfile = vlSymsp->_vm_contextp__->dumpfileCheck();\n");
            puts("vlSymsp->__Vm_dumperp->open(dumpfile.c_str());\n");
            puts("vlSymsp->__Vm_dumping = true;\n");
            puts("}\n");
            puts("}\n");
            splitSizeInc(10);

            puts("\nvoid " + topClassName() + "::_traceDumpClose() {\n");
            puts("const VerilatedLockGuard lock(vlSymsp->__Vm_dumperMutex);\n");
            puts("vlSymsp->__Vm_dumping = false;\n");
            puts("VL_DO_CLEAR(delete vlSymsp->__Vm_dumperp, vlSymsp->__Vm_dumperp = "
                 "nullptr);\n");
            puts("}\n");
            splitSizeInc(10);
        }

        puts("\n");
        m_lazyDecls.emit("void " + topClassName() + "__", protect("traceInitTop"),
                         "(" + topClassName() + "* vlSelf, " + v3Global.opt.traceClassBase()
                             + "* tracep);");

        puts("\nstatic void " + protect("traceInit") + "(void* voidSelf, "
             + v3Global.opt.traceClassBase() + "* tracep, uint32_t code) {\n");
        putsDecoration("// Callback from tracep->open()\n");
        puts(topClassName() + "*const __restrict vlSelf = static_cast<" + topClassName()
             + "*>(voidSelf);\n");
        puts("if (!vlSelf->vlSymsp->_vm_contextp__->calcUnusedSigs()) {\n");
        puts("VL_FATAL_MT(__FILE__, __LINE__, __FILE__,\n");
        puts("            \"Turning on wave traces requires Verilated::traceEverOn(true) call "
             "before time 0.\");\n");
        puts("}\n");
        puts("vlSelf->vlSymsp->__Vm_baseCode = code;\n");
        puts("tracep->module(vlSelf->vlSymsp->name());\n");
        puts("tracep->scopeEscape(' ');\n");
        puts(topClassName() + "__" + protect("traceInitTop") + "(vlSelf, tracep);\n");
        puts("tracep->scopeEscape('.');\n");  // Restore so later traced files won't break
        puts("}\n");
        splitSizeInc(10);

        puts("\n");
        m_lazyDecls.emit("void " + topClassName() + "__", protect("traceRegister"),
                         "(" + topClassName() + "* vlSelf, " + v3Global.opt.traceClassBase()
                             + "* tracep);");

        puts("\nvoid " + topClassName() + "::trace(");
        puts(v3Global.opt.traceClassBase() + "C* tfp, int, int) {\n");
        puts("tfp->spTrace()->addInitCb(&" + protect("traceInit") + ", this);\n");
        puts(topClassName() + "__" + protect("traceRegister") + "(this, tfp->spTrace());\n");
        puts("}\n");
        splitSizeInc(10);

        puts("\n//======================\n\n");
    }

    bool emitTraceIsScBv(AstTraceInc* nodep) {
        const AstVarRef* varrefp = VN_CAST(nodep->declp()->valuep(), VarRef);
        if (!varrefp) return false;
        AstVar* varp = varrefp->varp();
        return varp->isSc() && varp->isScBv();
    }

    bool emitTraceIsScBigUint(AstTraceInc* nodep) {
        const AstVarRef* varrefp = VN_CAST(nodep->declp()->valuep(), VarRef);
        if (!varrefp) return false;
        AstVar* varp = varrefp->varp();
        return varp->isSc() && varp->isScBigUint();
    }

    bool emitTraceIsScUint(AstTraceInc* nodep) {
        const AstVarRef* varrefp = VN_CAST(nodep->declp()->valuep(), VarRef);
        if (!varrefp) return false;
        AstVar* varp = varrefp->varp();
        return varp->isSc() && varp->isScUint();
    }

    void emitTraceInitOne(AstTraceDecl* nodep, int enumNum) {
        if (nodep->dtypep()->basicp()->isDouble()) {
            puts("tracep->declDouble");
        } else if (nodep->isWide()) {
            puts("tracep->declArray");
        } else if (nodep->isQuad()) {
            puts("tracep->declQuad");
        } else if (nodep->bitRange().ranged()) {
            puts("tracep->declBus");
        } else {
            puts("tracep->declBit");
        }

        puts("(c+" + cvtToStr(nodep->code()));
        if (nodep->arrayRange().ranged()) puts("+i*" + cvtToStr(nodep->widthWords()));
        puts(",");
        if (nodep->isScoped()) puts("Verilated::catName(scopep,");
        putsQuoted(VIdProtect::protectWordsIf(nodep->showname(), nodep->protect()));
        if (nodep->isScoped()) puts(",(int)scopet,\" \")");
        // Direction
        if (v3Global.opt.traceFormat().fst()) {
            puts("," + cvtToStr(enumNum));
            // fstVarDir
            if (nodep->declDirection().isInoutish()) {
                puts(",FST_VD_INOUT");
            } else if (nodep->declDirection().isWritable()) {
                puts(",FST_VD_OUTPUT");
            } else if (nodep->declDirection().isNonOutput()) {
                puts(",FST_VD_INPUT");
            } else {
                puts(", FST_VD_IMPLICIT");
            }
            //
            // fstVarType
            const AstVarType vartype = nodep->varType();
            const AstBasicDTypeKwd kwd = nodep->declKwd();
            string fstvt;
            // Doubles have special decoding properties, so must indicate if a double
            if (nodep->dtypep()->basicp()->isDouble()) {
                if (vartype == AstVarType::GPARAM || vartype == AstVarType::LPARAM) {
                    fstvt = "FST_VT_VCD_REAL_PARAMETER";
                } else {
                    fstvt = "FST_VT_VCD_REAL";
                }
            }
            // clang-format off
            else if (vartype == AstVarType::GPARAM) {  fstvt = "FST_VT_VCD_PARAMETER"; }
            else if (vartype == AstVarType::LPARAM) {  fstvt = "FST_VT_VCD_PARAMETER"; }
            else if (vartype == AstVarType::SUPPLY0) { fstvt = "FST_VT_VCD_SUPPLY0"; }
            else if (vartype == AstVarType::SUPPLY1) { fstvt = "FST_VT_VCD_SUPPLY1"; }
            else if (vartype == AstVarType::TRI0) {    fstvt = "FST_VT_VCD_TRI0"; }
            else if (vartype == AstVarType::TRI1) {    fstvt = "FST_VT_VCD_TRI1"; }
            else if (vartype == AstVarType::TRIWIRE) { fstvt = "FST_VT_VCD_TRI"; }
            else if (vartype == AstVarType::WIRE) {    fstvt = "FST_VT_VCD_WIRE"; }
            else if (vartype == AstVarType::PORT) {    fstvt = "FST_VT_VCD_WIRE"; }
            //
            else if (kwd == AstBasicDTypeKwd::INTEGER) {  fstvt = "FST_VT_VCD_INTEGER"; }
            else if (kwd == AstBasicDTypeKwd::BIT) {      fstvt = "FST_VT_SV_BIT"; }
            else if (kwd == AstBasicDTypeKwd::LOGIC) {    fstvt = "FST_VT_SV_LOGIC"; }
            else if (kwd == AstBasicDTypeKwd::INT) {      fstvt = "FST_VT_SV_INT"; }
            else if (kwd == AstBasicDTypeKwd::SHORTINT) { fstvt = "FST_VT_SV_SHORTINT"; }
            else if (kwd == AstBasicDTypeKwd::LONGINT) {  fstvt = "FST_VT_SV_LONGINT"; }
            else if (kwd == AstBasicDTypeKwd::BYTE) {     fstvt = "FST_VT_SV_BYTE"; }
            else { fstvt = "FST_VT_SV_BIT"; }
            // clang-format on
            //
            // Not currently supported
            // FST_VT_VCD_EVENT
            // FST_VT_VCD_PORT
            // FST_VT_VCD_SHORTREAL
            // FST_VT_VCD_REALTIME
            // FST_VT_VCD_SPARRAY
            // FST_VT_VCD_TRIAND
            // FST_VT_VCD_TRIOR
            // FST_VT_VCD_TRIREG
            // FST_VT_VCD_WAND
            // FST_VT_VCD_WOR
            // FST_VT_SV_ENUM
            // FST_VT_GEN_STRING
            puts("," + fstvt);
        }
        // Range
        if (nodep->arrayRange().ranged()) {
            puts(", true,(i+" + cvtToStr(nodep->arrayRange().lo()) + ")");
        } else {
            puts(", false,-1");
        }
        if (!nodep->dtypep()->basicp()->isDouble() && nodep->bitRange().ranged()) {
            puts(", " + cvtToStr(nodep->bitRange().left()) + ","
                 + cvtToStr(nodep->bitRange().right()));
        }
        puts(");");
    }

    int emitTraceDeclDType(AstNodeDType* nodep) {
        // Return enum number or -1 for none
        if (v3Global.opt.traceFormat().fst()) {
            // Skip over refs-to-refs, but stop before final ref so can get data type name
            // Alternatively back in V3Width we could push enum names from upper typedefs
            if (AstEnumDType* enump = VN_CAST(nodep->skipRefToEnump(), EnumDType)) {
                int enumNum = enump->user1();
                if (!enumNum) {
                    enumNum = ++m_enumNum;
                    enump->user1(enumNum);
                    int nvals = 0;
                    puts("{\n");
                    puts("const char* " + protect("__VenumItemNames") + "[]\n");
                    puts("= {");
                    for (AstEnumItem* itemp = enump->itemsp(); itemp;
                         itemp = VN_CAST(itemp->nextp(), EnumItem)) {
                        if (++nvals > 1) puts(", ");
                        putbs("\"" + itemp->prettyName() + "\"");
                    }
                    puts("};\n");
                    nvals = 0;
                    puts("const char* " + protect("__VenumItemValues") + "[]\n");
                    puts("= {");
                    for (AstEnumItem* itemp = enump->itemsp(); itemp;
                         itemp = VN_CAST(itemp->nextp(), EnumItem)) {
                        AstConst* constp = VN_CAST(itemp->valuep(), Const);
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
        iterateAndNextNull(nodep->precondsp());
        const string func = nodep->full() ? "full" : "chg";
        bool emitWidth = true;
        if (nodep->dtypep()->basicp()->isDouble()) {
            puts("tracep->" + func + "Double");
            emitWidth = false;
        } else if (nodep->isWide() || emitTraceIsScBv(nodep) || emitTraceIsScBigUint(nodep)) {
            puts("tracep->" + func + "WData");
        } else if (nodep->isQuad()) {
            puts("tracep->" + func + "QData");
        } else if (nodep->declp()->widthMin() > 16) {
            puts("tracep->" + func + "IData");
        } else if (nodep->declp()->widthMin() > 8) {
            puts("tracep->" + func + "SData");
        } else if (nodep->declp()->widthMin() > 1) {
            puts("tracep->" + func + "CData");
        } else {
            puts("tracep->" + func + "Bit");
            emitWidth = false;
        }

        const uint32_t offset = (arrayindex < 0) ? 0 : (arrayindex * nodep->declp()->widthWords());
        const uint32_t code = nodep->declp()->code() + offset;
        puts(v3Global.opt.trueTraceThreads() && !nodep->full() ? "(base+" : "(oldp+");
        puts(cvtToStr(code - m_baseCode));
        puts(",");
        emitTraceValue(nodep, arrayindex);
        if (emitWidth) puts("," + cvtToStr(nodep->declp()->widthMin()));
        puts(");\n");
    }
    void emitTraceValue(AstTraceInc* nodep, int arrayindex) {
        if (AstVarRef* const varrefp = VN_CAST(nodep->valuep(), VarRef)) {
            AstVar* varp = varrefp->varp();
            puts("(");
            if (emitTraceIsScBigUint(nodep)) {
                puts("(vluint32_t*)");
            } else if (emitTraceIsScBv(nodep)) {
                puts("VL_SC_BV_DATAP(");
            }
            iterate(varrefp);  // Put var name out
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
            iterate(nodep->valuep());
            puts(")");
        }
    }

    // VISITORS
    using EmitCFunc::visit;  // Suppress hidden overloaded virtual function warning
    virtual void visit(AstNetlist* nodep) override {
        // Top module only
        iterate(nodep->topModulep());
    }
    virtual void visit(AstNodeModule* nodep) override {
        m_modp = nodep;
        iterateChildren(nodep);
        m_modp = nullptr;
    }
    virtual void visit(AstCFunc* nodep) override {
        if (nodep->slow() != m_slow) return;
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_useSelfForThis);
        if (nodep->funcType().isTrace()) {  // TRACE_*
            m_cfuncp = nodep;

            if (splitNeeded()) {
                // Splitting file, so using parallel build.
                v3Global.useParallelBuild(true);
                // Close old file
                VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
                // Open a new file
                newOutCFile(splitFilenumInc());
            }

            splitSizeInc(nodep);

            puts("\n");
            m_lazyDecls.emit(nodep);
            emitCFuncHeader(nodep, m_modp, /* withScope: */ true);
            puts(" {\n");

            if (nodep->isLoose()) {
                m_lazyDecls.declared(nodep);  // Defined here, so no longer needs declaration
                if (!nodep->isStatic()) {  // Standard prologue
                    puts("if (false && vlSelf) {}  // Prevent unused\n");
                    m_useSelfForThis = true;
                    puts(symClassAssign());
                }
            }

            if (nodep->initsp()) {
                string section;
                emitVarList(nodep->initsp(), EVL_FUNC_ALL, "", section /*ref*/);
                iterateAndNextNull(nodep->initsp());
            }

            m_baseCode = -1;

            if (nodep->funcType() == AstCFuncType::TRACE_CHANGE_SUB) {
                const AstNode* const stmtp = nodep->stmtsp();
                const AstIf* const ifp = VN_CAST_CONST(stmtp, If);
                const AstTraceInc* const tracep
                    = VN_CAST_CONST(ifp ? ifp->ifsp() : stmtp, TraceInc);
                // On rare occasions we can end up with an empty sub function
                m_baseCode = tracep ? tracep->declp()->code() : 0;
                if (v3Global.opt.trueTraceThreads()) {
                    puts("const vluint32_t base = vlSymsp->__Vm_baseCode + " + cvtToStr(m_baseCode)
                         + ";\n");
                    puts("if (false && tracep && base) {}  // Prevent unused\n");
                } else {
                    puts("vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode + "
                         + cvtToStr(m_baseCode) + ");\n");
                    puts("if (false && oldp) {}  // Prevent unused\n");
                }
            } else if (nodep->funcType() == AstCFuncType::TRACE_FULL_SUB) {
                m_baseCode = 0;
                puts("vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode);\n");
                puts("if (false && oldp) {}  // Prevent unused\n");
            } else if (nodep->funcType() == AstCFuncType::TRACE_INIT_SUB) {
                puts("const int c = vlSymsp->__Vm_baseCode;\n");
                puts("if (false && tracep && c) {}  // Prevent unused\n");
            }

            if (nodep->stmtsp()) {
                putsDecoration("// Body\n");
                puts("{\n");
                iterateAndNextNull(nodep->stmtsp());
                puts("}\n");
            }
            if (nodep->finalsp()) {
                putsDecoration("// Final\n");
                iterateAndNextNull(nodep->finalsp());
            }
            puts("}\n");
        }
    }
    virtual void visit(AstTraceDecl* nodep) override {
        const int enumNum = emitTraceDeclDType(nodep->dtypep());
        if (nodep->arrayRange().ranged()) {
            puts("{int i; for (i=0; i<" + cvtToStr(nodep->arrayRange().elements()) + "; i++) {\n");
            emitTraceInitOne(nodep, enumNum);
            puts("}}\n");
        } else {
            emitTraceInitOne(nodep, enumNum);
            puts("\n");
        }
    }
    virtual void visit(AstTraceInc* nodep) override {
        if (nodep->declp()->arrayRange().ranged()) {
            // It traces faster if we unroll the loop
            for (int i = 0; i < nodep->declp()->arrayRange().elements(); i++) {
                emitTraceChangeOne(nodep, i);
            }
        } else {
            emitTraceChangeOne(nodep, -1);
        }
    }
    virtual void visit(AstCoverDecl* nodep) override {}
    virtual void visit(AstCoverInc* nodep) override {}

public:
    explicit EmitCTrace(bool slow)
        : m_slow{slow} {}
    virtual ~EmitCTrace() override = default;
    void main() {
        // Put out the file
        newOutCFile(0);

        if (m_slow) emitTraceSlow();

        iterate(v3Global.rootp());

        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
};

//######################################################################
// EmitC class functions

static void setParentClassPointers() {
    // Set user4p in all CFunc and Var to point to the containing AstNodeModule
    const auto setAll = [](AstNodeModule* modp) -> void {
        for (AstNode* nodep = VN_CAST(modp, NodeModule)->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, CFunc) || VN_IS(nodep, Var)) nodep->user4p(modp);
        }
    };
    for (AstNode* modp = v3Global.rootp()->modulesp(); modp; modp = modp->nextp()) {
        setAll(VN_CAST(modp, NodeModule));
    }
    setAll(v3Global.rootp()->constPoolp()->modp());
}

void V3EmitC::emitc() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Set user4 to parent module
    AstUser4InUse user4InUse;
    setParentClassPointers();
    // Process each module in turn
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep;
         nodep = VN_CAST(nodep->nextp(), NodeModule)) {
        if (VN_IS(nodep, Class)) continue;  // Imped with ClassPackage
        {
            EmitCImp cint;
            cint.mainInt(nodep);
            cint.mainImp(nodep, true);
        }
        {
            EmitCImp fast;
            fast.mainImp(nodep, false);
        }
    }
}

void V3EmitC::emitcTrace() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    if (v3Global.opt.trace()) {
        // Set user4 to parent module
        AstUser4InUse user4InUse;
        setParentClassPointers();
        {
            EmitCTrace slow(true);
            slow.main();
        }
        {
            EmitCTrace fast(false);
            fast.main();
        }
    }
}

void V3EmitC::emitcFiles() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    for (AstNodeFile* filep = v3Global.rootp()->filesp(); filep;
         filep = VN_CAST(filep->nextp(), NodeFile)) {
        AstCFile* cfilep = VN_CAST(filep, CFile);
        if (cfilep && cfilep->tblockp()) {
            V3OutCFile of(cfilep->name());
            of.puts("// DESCR"
                    "IPTION: Verilator generated C++\n");
            EmitCFunc visitor(cfilep->tblockp(), &of, true);
        }
    }
}
