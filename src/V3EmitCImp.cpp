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

//######################################################################
// Internal EmitC implementation

class EmitCImp final : EmitCFunc {
    // MEMBERS
    const AstNodeModule* const m_fileModp;  // Files names/headers constructed using this module
    const bool m_slow;  // Creating __Slow file

    // METHODS
    void openNextOutputFile() {
        UASSERT(!m_ofp, "Output file already open");

        m_lazyDecls.reset();  // Need to emit new lazy declarations

        if (v3Global.opt.lintOnly()) {
            // Unfortunately we have some lint checks here, so we can't just skip processing.
            // We should move them to a different stage.
            const string filename = VL_DEV_NULL;
            newCFile(filename, /* slow: */ m_slow, /* source: */ true);
            m_ofp = new V3OutCFile(filename);
        } else {
            string filename = v3Global.opt.makeDir() + "/" + prefixNameProtect(m_fileModp);
            if (const int filenum = splitFilenumInc()) filename += "__" + cvtToStr(filenum);
            if (m_slow) filename += "__Slow";
            filename += ".cpp";
            newCFile(filename, /* slow: */ m_slow, /* source: */ true);
            m_ofp = v3Global.opt.systemC() ? new V3OutScFile(filename) : new V3OutCFile(filename);
        }

        ofp()->putsHeader();
        puts("// DESCRIPTION: Verilator output: Design implementation internals\n");
        puts("// See " + topClassName() + ".h for the primary calling header\n");

        // Include files
        puts("\n");
        puts("#include \"" + prefixNameProtect(m_fileModp) + ".h\"\n");
        puts("#include \"" + symClassName() + ".h\"\n");

        if (v3Global.dpi()) {
            puts("\n");
            puts("#include \"verilated_dpi.h\"\n");
        }

        emitModCUse(m_fileModp, VUseType::IMP_INCLUDE);
        emitModCUse(m_fileModp, VUseType::IMP_FWD_CLASS);

        emitTextSection(m_modp, AstType::atScImpHdr);
    }

    void emitParamDefns(const AstNodeModule* modp) {
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) {
                if (varp->isParam() && (varp->isUsedParam() || varp->isSigPublic())) {
                    UASSERT_OBJ(varp->valuep(), nodep, "No init for a param?");
                    // These should be static const values, however older MSVC++ did't
                    // support them; should be ok now under C++11, need to refactor.
                    if (varp->isWide()) {  // Unsupported for output
                    } else if (varp->isString()) {
                        puts("const std::string ");
                        puts(prefixNameProtect(modp) + "::" + protect("var_" + varp->name())
                             + "(");
                        iterateAndNextNull(varp->valuep());
                        puts(");\n");
                    } else if (!VN_IS(varp->valuep(), Const)) {  // Unsupported for output
                        // putsDecoration("// enum ..... "+varp->nameProtect()
                        //               +"not simple value, see variable above instead");
                    } else if (VN_IS(varp->dtypep(), BasicDType)
                               && VN_CAST(varp->dtypep(), BasicDType)
                                      ->isOpaque()) {  // Can't put out e.g. doubles
                    } else {
                        puts(varp->isQuad() ? "const QData " : "const IData ");
                        puts(prefixNameProtect(modp) + "::" + protect("var_" + varp->name())
                             + "(");
                        iterateAndNextNull(varp->valuep());
                        puts(");\n");
                    }
                }
            }
        }
    }
    void emitCtorImp(const AstNodeModule* modp) {
        const string modName = prefixNameProtect(modp);

        puts("\n");
        m_lazyDecls.emit("void " + modName + "__", protect("_ctor_var_reset"),
                         "(" + modName + "* vlSelf);");
        puts("\n");

        puts(modName + "::" + modName + "(const char* _vcname__)\n");
        puts("    : VerilatedModule(_vcname__)\n");

        ofp()->indentInc();
        for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) {
                if (const AstBasicDType* const dtypep
                    = VN_CAST(varp->dtypeSkipRefp(), BasicDType)) {
                    if (dtypep->keyword().isMTaskState()) {
                        puts(", ");
                        puts(varp->nameProtect());
                        puts("(");
                        iterate(varp->valuep());
                        puts(")\n");
                    } else if (varp->isIO() && varp->isSc()) {
                        puts(", ");
                        puts(varp->nameProtect());
                        puts("(");
                        putsQuoted(varp->nameProtect());
                        puts(")\n");
                    }
                }
            }
        }
        ofp()->indentDec();

        puts(" {\n");

        putsDecoration("// Reset structure values\n");
        puts(modName + "__" + protect("_ctor_var_reset") + "(this);\n");
        emitTextSection(modp, AstType::atScCtor);

        puts("}\n");
    }
    void emitConfigureImp(const AstNodeModule* modp) {
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
    void emitCoverageImp() {
        if (v3Global.opt.coverage()) {
            puts("\n// Coverage\n");
            // Rather than putting out VL_COVER_INSERT calls directly, we do it via this function
            // This gets around gcc slowness constructing all of the template arguments.
            puts("void " + prefixNameProtect(m_modp) + "::__vlCoverInsert(");
            puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
            puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
            puts("const char* hierp, const char* pagep, const char* commentp, const char* "
                 "linescovp) "
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
    void emitDestructorImp(const AstNodeModule* modp) {
        puts("\n");
        puts(prefixNameProtect(modp) + "::~" + prefixNameProtect(modp) + "() {\n");
        emitTextSection(modp, AstType::atScDtor);
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

                puts("}\n");
            }
        }
    }
    void emitAll(const AstNodeModule* modp) {
        if (m_slow) {
            // Emit static variable definitions
            const string modName = prefixNameProtect(modp);
            for (const AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
                if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) {
                    if (varp->isStatic()) {
                        puts(varp->vlArgType(true, false, false, modName));
                        puts(";\n");
                    }
                }
            }

            if (!VN_IS(modp, Class)) {
                emitParamDefns(modp);
                emitCtorImp(modp);
                emitConfigureImp(modp);
                emitDestructorImp(modp);
            }
            emitSavableImp(modp);
            emitCoverageImp();
        } else {
            emitTextSection(modp, AstType::atScImp);
        }

        // Emit all AstCFunc
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstCFunc* const funcp = VN_CAST(nodep, CFunc)) iterate(funcp);
        }
    }

    // VISITORS
    virtual void visit(AstCFunc* nodep) override {
        // TRACE_* and DPI handled elsewhere
        if (nodep->isTrace()) return;
        if (nodep->dpiImportPrototype()) return;
        if (nodep->dpiExportDispatcher()) return;
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

    explicit EmitCImp(const AstNodeModule* modp, bool slow)
        : m_fileModp{modp}
        , m_slow{slow} {
        UINFO(5, "  Emitting implementation of " << prefixNameProtect(modp) << endl);

        m_modp = modp;

        openNextOutputFile();

        emitAll(modp);

        if (const AstClassPackage* const packagep = VN_CAST_CONST(modp, ClassPackage)) {
            // Put the non-static class implementation in same C++ files as
            // often optimizations are possible when both are seen by the
            // compiler together
            m_modp = packagep->classp();
            emitAll(packagep->classp());
        }

        // Close output file
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
    virtual ~EmitCImp() override = default;

public:
    static void main(const AstNodeModule* modp, bool slow) { EmitCImp{modp, slow}; }
};

//######################################################################
// Tracing routines

class EmitCTrace final : EmitCFunc {
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user1() -> int.  Enum number
    AstUser1InUse m_inuser1;

    // MEMBERS
    const bool m_slow;  // Making slow file
    int m_enumNum = 0;  // Enumeration number (whole netlist)

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

        // Includes
        puts("#include \"" + v3Global.opt.traceSourceLang() + ".h\"\n");
        puts("#include \"" + symClassName() + ".h\"\n");
        puts("\n");
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
        puts(cvtToStr(code - nodep->baseCode()));
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
    virtual void visit(AstCFunc* nodep) override {
        if (!nodep->isTrace()) return;
        if (nodep->slow() != m_slow) return;

        if (splitNeeded()) {
            // Splitting file, so using parallel build.
            v3Global.useParallelBuild(true);
            // Close old file
            VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
            // Open a new file
            newOutCFile(splitFilenumInc());
        }

        EmitCFunc::visit(nodep);
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

    explicit EmitCTrace(AstNodeModule* modp, bool slow)
        : m_slow{slow} {
        m_modp = modp;
        // Open output file
        newOutCFile(splitFilenumInc());
        // Emit functions
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstCFunc* const funcp = VN_CAST(nodep, CFunc)) { iterate(funcp); }
        }
        // Close output file
        VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
    }
    virtual ~EmitCTrace() override = default;

public:
    static void main(AstNodeModule* modp, bool slow) { EmitCTrace{modp, slow}; }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcImp() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // Set user4p in all CFunc and Var to point to the containing AstNodeModule
    AstUser4InUse user4InUse;
    const auto setAll = [](AstNodeModule* modp) -> void {
        for (AstNode* nodep = VN_CAST(modp, NodeModule)->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, CFunc) || VN_IS(nodep, Var)) nodep->user4p(modp);
        }
    };
    for (AstNode* modp = v3Global.rootp()->modulesp(); modp; modp = modp->nextp()) {
        setAll(VN_CAST(modp, NodeModule));
    }
    setAll(v3Global.rootp()->constPoolp()->modp());

    // Process each module in turn
    for (const AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Class)) continue;  // Imped with ClassPackage
        const AstNodeModule* const modp = VN_CAST_CONST(nodep, NodeModule);
        EmitCImp::main(modp, /* slow: */ true);
        EmitCImp::main(modp, /* slow: */ false);
    }

    // Emit trace routines (currently they can only exist in the top module)
    if (v3Global.opt.trace() && !v3Global.opt.lintOnly()) {
        EmitCTrace::main(v3Global.rootp()->topModulep(), /* slow: */ true);
        EmitCTrace::main(v3Global.rootp()->topModulep(), /* slow: */ false);
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
