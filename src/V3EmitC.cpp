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
#include "V3String.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3Number.h"
#include "V3PartitionGraph.h"
#include "V3Task.h"
#include "V3TSP.h"

#include <algorithm>
#include <map>
#include <vector>
#include <unordered_set>

constexpr int VL_VALUE_STRING_MAX_WIDTH = 8192;  // We use a static char array in VL_VALUE_STRING

constexpr int EMITC_NUM_CONSTW
    = 8;  // Number of VL_CONST_W_*X's in verilated.h (IE VL_CONST_W_8X is last)

//######################################################################
// Emit statements and math operators

class EmitCStmts VL_NOT_FINAL : public EmitCBaseVisitor {
private:
    using VarVec = std::vector<const AstVar*>;
    using VarSortMap = std::map<int, VarVec>;  // Map size class to VarVec

    bool m_suppressSemi;
    AstVarRef* m_wideTempRefp;  // Variable that _WW macros should be setting
    VarVec m_ctorVarsVec;  // All variables in constructor order
    int m_labelNum;  // Next label number
    int m_splitSize;  // # of cfunc nodes placed into output file
    int m_splitFilenum;  // File number being created, 0 = primary

public:
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // ACCESSORS
    int splitFilenum() const { return m_splitFilenum; }
    int splitFilenumInc() {
        m_splitSize = 0;
        return ++m_splitFilenum;
    }
    int splitSize() const { return m_splitSize; }
    void splitSizeInc(int count) { m_splitSize += count; }
    void splitSizeInc(AstNode* nodep) { splitSizeInc(EmitCBaseCounterVisitor(nodep).count()); }
    bool splitNeeded() const {
        return (splitSize() && v3Global.opt.outputSplit()
                && v3Global.opt.outputSplit() < splitSize());
    }

    // METHODS
    void displayNode(AstNode* nodep, AstScopeName* scopenamep, const string& vformat,
                     AstNode* exprsp, bool isScan);
    void displayEmit(AstNode* nodep, bool isScan);
    void displayArg(AstNode* dispp, AstNode** elistp, bool isScan, const string& vfmt, bool ignore,
                    char fmtLetter);

    void emitVarDecl(const AstVar* nodep, const string& prefixIfImp);
    enum EisWhich : uint8_t {
        EVL_CLASS_IO,
        EVL_CLASS_SIG,
        EVL_CLASS_TEMP,
        EVL_CLASS_PAR,
        EVL_CLASS_ALL,
        EVL_FUNC_ALL
    };
    void emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp, string& sectionr);
    static void emitVarSort(const VarSortMap& vmap, VarVec* sortedp);
    void emitSortedVarList(const VarVec& anons, const VarVec& nonanons, const string& prefixIfImp);
    void emitVarCtors(bool* firstp);
    void emitCtorSep(bool* firstp);
    bool emitSimpleOk(AstNodeMath* nodep);
    void emitIQW(AstNode* nodep) {
        // Other abbrevs: "C"har, "S"hort, "F"loat, "D"ouble, stri"N"g
        puts(nodep->dtypep()->charIQWN());
    }
    void emitScIQW(AstVar* nodep) {
        UASSERT_OBJ(nodep->isSc(), nodep, "emitting SystemC operator on non-SC variable");
        // clang-format off
        puts(nodep->isScBigUint() ? "SB"
             : nodep->isScUint()  ? "SU"
             : nodep->isScBv()    ? "SW"
             : (nodep->isScQuad() ? "SQ" : "SI"));
        // clang-format on
    }
    void emitDatap(AstNode* nodep) {
        // When passing to a function with va_args the compiler doesn't
        // know need a pointer so when wide, need to look inside VlWide
        if (nodep->isWide()) puts(".data()");
    }

    void emitOpName(AstNode* nodep, const string& format, AstNode* lhsp, AstNode* rhsp,
                    AstNode* thsp);
    void emitDeclArrayBrackets(const AstVar* nodep) {
        // This isn't very robust and may need cleanup for other data types
        for (const AstUnpackArrayDType* arrayp
             = VN_CAST_CONST(nodep->dtypeSkipRefp(), UnpackArrayDType);
             arrayp; arrayp = VN_CAST_CONST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
            puts("[" + cvtToStr(arrayp->elementsConst()) + "]");
        }
    }
    void emitVarCmtChg(const AstVar* varp, string* curVarCmtp) {
        string newVarCmt = varp->mtasksString();
        if (*curVarCmtp != newVarCmt) {
            *curVarCmtp = newVarCmt;
            if (v3Global.opt.threads()) puts("// Begin mtask footprint " + *curVarCmtp + "\n");
        }
    }
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

    struct CmpName {
        bool operator()(const AstNode* lhsp, const AstNode* rhsp) const {
            return lhsp->name() < rhsp->name();
        }
    };
    void emitIntFuncDecls(AstNodeModule* modp, bool methodFuncs) {
        std::vector<const AstCFunc*> funcsp;

        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstCFunc* funcp = VN_CAST(nodep, CFunc)) {
                if (!funcp->skipDecl() && funcp->isMethod() == methodFuncs
                    && !funcp->dpiImport()) {  // DPI is prototyped in __Dpi.h
                    funcsp.push_back(funcp);
                }
            }
        }

        stable_sort(funcsp.begin(), funcsp.end(), CmpName());

        for (const AstCFunc* funcp : funcsp) {
            ofp()->putsPrivate(funcp->declPrivate());
            if (!funcp->ifdef().empty()) puts("#ifdef " + funcp->ifdef() + "\n");
            if (funcp->isStatic().trueUnknown()) puts("static ");
            if (funcp->isVirtual()) puts("virtual ");
            if (!funcp->isConstructor() && !funcp->isDestructor()) {
                puts(funcp->rtnTypeVoid());
                puts(" ");
            }
            puts(funcNameProtect(funcp, modp));
            puts("(" + cFuncArgs(funcp) + ")");
            if (funcp->isConst().trueKnown()) puts(" const");
            if (funcp->slow()) puts(" VL_ATTR_COLD");
            puts(";\n");
            if (!funcp->ifdef().empty()) puts("#endif  // " + funcp->ifdef() + "\n");
        }

        if (methodFuncs && modp->isTop() && v3Global.opt.mtasks()) {
            // Emit the mtask func prototypes.
            AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
            UASSERT_OBJ(execGraphp, v3Global.rootp(), "Root should have an execGraphp");
            const V3Graph* depGraphp = execGraphp->depGraphp();
            for (const V3GraphVertex* vxp = depGraphp->verticesBeginp(); vxp;
                 vxp = vxp->verticesNextp()) {
                const ExecMTask* mtp = dynamic_cast<const ExecMTask*>(vxp);
                if (mtp->threadRoot()) {
                    // Emit function declaration for this mtask
                    ofp()->putsPrivate(true);
                    puts("static void ");
                    puts(protect(mtp->cFuncName()));
                    puts("(bool even_cycle, void* symtab);\n");
                }
            }
            // No AstCFunc for this one, as it's synthetic. Just write it:
            puts("static void __Vmtask__final(bool even_cycle, void* symtab);\n");
        }
    }
    void ccallIterateArgs(AstNodeCCall* nodep) {
        puts(nodep->argTypes());
        bool comma = (nodep->argTypes() != "");
        for (AstNode* subnodep = nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
            if (comma) puts(", ");
            iterate(subnodep);
            comma = true;
        }
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        bool paren = true;
        bool decind = false;
        if (AstSel* selp = VN_CAST(nodep->lhsp(), Sel)) {
            if (selp->widthMin() == 1) {
                putbs("VL_ASSIGNBIT_");
                emitIQW(selp->fromp());
                if (nodep->rhsp()->isAllOnesV()) {
                    puts("O(");
                } else {
                    puts("I(");
                }
                puts(cvtToStr(nodep->widthMin()) + ",");
                iterateAndNextNull(selp->lsbp());
                puts(", ");
                iterateAndNextNull(selp->fromp());
                puts(", ");
            } else {
                putbs("VL_ASSIGNSEL_");
                emitIQW(selp->fromp());
                puts("II");
                emitIQW(nodep->rhsp());
                puts("(");
                puts(cvtToStr(selp->fromp()->widthMin()) + ",");
                puts(cvtToStr(nodep->widthMin()) + ",");
                iterateAndNextNull(selp->lsbp());
                puts(", ");
                iterateAndNextNull(selp->fromp());
                puts(", ");
            }
        } else if (AstGetcRefN* selp = VN_CAST(nodep->lhsp(), GetcRefN)) {
            iterateAndNextNull(selp->lhsp());
            puts(" = ");
            putbs("VL_PUTC_N(");
            iterateAndNextNull(selp->lhsp());
            puts(", ");
            iterateAndNextNull(selp->rhsp());
            puts(", ");
        } else if (AstVar* varp = AstVar::scVarRecurse(nodep->lhsp())) {
            putbs("VL_ASSIGN_");  // Set a systemC variable
            emitScIQW(varp);
            emitIQW(nodep);
            puts("(");
            puts(cvtToStr(nodep->widthMin()) + ",");
            iterateAndNextNull(nodep->lhsp());
            puts(", ");
        } else if (AstVar* varp = AstVar::scVarRecurse(nodep->rhsp())) {
            putbs("VL_ASSIGN_");  // Get a systemC variable
            emitIQW(nodep);
            emitScIQW(varp);
            puts("(");
            puts(cvtToStr(nodep->widthMin()) + ",");
            iterateAndNextNull(nodep->lhsp());
            puts(", ");
        } else if (nodep->isWide() && VN_IS(nodep->lhsp(), VarRef)  //
                   && !VN_IS(nodep->rhsp(), CMath)  //
                   && !VN_IS(nodep->rhsp(), CMethodHard)  //
                   && !VN_IS(nodep->rhsp(), VarRef)  //
                   && !VN_IS(nodep->rhsp(), AssocSel)  //
                   && !VN_IS(nodep->rhsp(), ArraySel)) {
            // Wide functions assign into the array directly, don't need separate assign statement
            m_wideTempRefp = VN_CAST(nodep->lhsp(), VarRef);
            paren = false;
        } else if (nodep->isWide()) {
            putbs("VL_ASSIGN_W(");
            puts(cvtToStr(nodep->widthMin()) + ",");
            iterateAndNextNull(nodep->lhsp());
            puts(", ");
        } else {
            paren = false;
            iterateAndNextNull(nodep->lhsp());
            puts(" ");
            ofp()->blockInc();
            decind = true;
            if (!VN_IS(nodep->rhsp(), Const)) ofp()->putBreak();
            puts("= ");
        }
        iterateAndNextNull(nodep->rhsp());
        if (paren) puts(")");
        if (decind) ofp()->blockDec();
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAlwaysPublic*) override {}
    virtual void visit(AstAssocSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        putbs(".at(");
        AstAssocArrayDType* adtypep = VN_CAST(nodep->fromp()->dtypep(), AssocArrayDType);
        UASSERT_OBJ(adtypep, nodep, "Associative select on non-associative type");
        if (adtypep->keyDTypep()->isWide()) {
            emitCvtWideArray(nodep->bitp(), nodep->fromp());
        } else {
            iterateAndNextNull(nodep->bitp());
        }
        puts(")");
    }
    virtual void visit(AstNodeCCall* nodep) override {
        if (AstCMethodCall* ccallp = VN_CAST(nodep, CMethodCall)) {
            // make this a Ast type for future opt
            iterate(ccallp->fromp());
            putbs("->");
        } else {
            puts(nodep->hiernameProtect());
        }
        puts(nodep->funcp()->nameProtect());
        puts("(");
        ccallIterateArgs(nodep);
        if (VN_IS(nodep->backp(), NodeMath) || VN_IS(nodep->backp(), CReturn)) {
            // We should have a separate CCall for math and statement usage, but...
            puts(")");
        } else {
            puts(");\n");
        }
    }
    virtual void visit(AstCMethodHard* nodep) override {
        iterate(nodep->fromp());
        puts(".");
        puts(nodep->nameProtect());
        puts("(");
        bool comma = false;
        for (AstNode* subnodep = nodep->pinsp(); subnodep; subnodep = subnodep->nextp()) {
            if (comma) puts(", ");
            // handle wide arguments to the queues
            if (VN_IS(nodep->fromp()->dtypep(), QueueDType) && subnodep->dtypep()->isWide()) {
                emitCvtWideArray(subnodep, nodep->fromp());
            } else {
                iterate(subnodep);
            }
            comma = true;
        }
        puts(")");
        // Some are statements some are math.
        if (nodep->isStatement()) puts(";\n");
        UASSERT_OBJ(!nodep->isStatement() || VN_IS(nodep->dtypep(), VoidDType), nodep,
                    "Statement of non-void data type");
    }
    virtual void visit(AstLambdaArgRef* nodep) override { putbs(nodep->nameProtect()); }
    virtual void visit(AstWith* nodep) override {
        // With uses a C++11 lambda
        putbs("[=](");
        if (auto* argrefp = nodep->indexArgRefp()) {
            putbs(argrefp->dtypep()->cType(argrefp->nameProtect(), false, false));
            puts(",");
        }
        if (auto* argrefp = nodep->valueArgRefp()) {
            putbs(argrefp->dtypep()->cType(argrefp->nameProtect(), false, false));
        }
        // Probably fragile, V3Task may need to convert to a AstCReturn
        puts(") { return ");
        iterateAndNextNull(nodep->exprp());
        puts("; }\n");
    }
    virtual void visit(AstIntfRef* nodep) override {
        putsQuoted(VIdProtect::protectWordsIf(AstNode::vcdName(nodep->name()), nodep->protect()));
    }
    virtual void visit(AstNodeCase* nodep) override {  // LCOV_EXCL_LINE
        // In V3Case...
        nodep->v3fatalSrc("Case statements should have been reduced out");
    }
    virtual void visit(AstComment* nodep) override {
        string at;
        if (nodep->showAt()) {
            at = " at " + nodep->fileline()->ascii();
            // If protecting, passthru less information about the design
            if (!v3Global.opt.protectIds()) return;
        }
        if (!(nodep->protect() && v3Global.opt.protectIds())) {
            putsDecoration(string("// ") + nodep->name() + at + "\n");
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) override {
        puts("self->__vlCoverInsert(");  // As Declared in emitCoverageDecl
        puts("&(vlSymsp->__Vcoverage[");
        puts(cvtToStr(nodep->dataDeclThisp()->binNum()));
        puts("])");
        // If this isn't the first instantiation of this module under this
        // design, don't really count the bucket, and rely on verilator_cov to
        // aggregate counts.  This is because Verilator combines all
        // hierarchies itself, and if verilator_cov also did it, you'd end up
        // with (number-of-instant) times too many counts in this bin.
        puts(", first");  // Enable, passed from __Vconfigure parameter
        puts(", ");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(", ");
        puts(cvtToStr(nodep->offset() + nodep->fileline()->firstColumn()));
        puts(", ");
        putsQuoted((!nodep->hier().empty() ? "." : "")
                   + protectWordsIf(nodep->hier(), nodep->protect()));
        puts(", ");
        putsQuoted(protectWordsIf(nodep->page(), nodep->protect()));
        puts(", ");
        putsQuoted(protectWordsIf(nodep->comment(), nodep->protect()));
        puts(", ");
        putsQuoted(nodep->linescov());
        puts(");\n");
    }
    virtual void visit(AstCoverInc* nodep) override {
        if (v3Global.opt.threads()) {
            puts("vlSymsp->__Vcoverage[");
            puts(cvtToStr(nodep->declp()->dataDeclThisp()->binNum()));
            puts("].fetch_add(1, std::memory_order_relaxed);\n");
        } else {
            puts("++(vlSymsp->__Vcoverage[");
            puts(cvtToStr(nodep->declp()->dataDeclThisp()->binNum()));
            puts("]);\n");
        }
    }
    virtual void visit(AstCReturn* nodep) override {
        puts("return (");
        iterateAndNextNull(nodep->lhsp());
        puts(");\n");
    }
    virtual void visit(AstDisplay* nodep) override {
        string text = nodep->fmtp()->text();
        if (nodep->addNewline()) text += "\n";
        displayNode(nodep, nodep->fmtp()->scopeNamep(), text, nodep->fmtp()->exprsp(), false);
    }
    virtual void visit(AstDumpCtl* nodep) override {
        switch (nodep->ctlType()) {
        case VDumpCtlType::FILE:
            puts("vlSymsp->_vm_contextp__->dumpfile(");
            emitCvtPackStr(nodep->exprp());
            puts(");\n");
            break;
        case VDumpCtlType::VARS:
            // We ignore number of levels to dump in exprp()
            if (v3Global.opt.trace()) {
                puts("vlSymsp->TOPp->_traceDumpOpen();\n");
            } else {
                puts("VL_PRINTF_MT(\"-Info: ");
                puts(protect(nodep->fileline()->filename()));
                puts(":");
                puts(cvtToStr(nodep->fileline()->lineno()));
                puts(": $dumpvar ignored, as Verilated without --trace");
                puts("\\n\");\n");
            }
            break;
        case VDumpCtlType::ALL:
            // $dumpall currently ignored
            break;
        case VDumpCtlType::FLUSH:
            // $dumpall currently ignored; would need rework of VCD single thread,
            // or flag we pass-through to next eval() iteration
            break;
        case VDumpCtlType::LIMIT:
            // $dumplimit currently ignored
            break;
        case VDumpCtlType::OFF:
            // Currently ignored as both Vcd and Fst do not support them, as would need "X" dump
            break;
        case VDumpCtlType::ON:
            // Currently ignored as $dumpoff is also ignored
            break;
        default: nodep->v3fatalSrc("Bad case, unexpected " << nodep->ctlType().ascii());
        }
    }
    virtual void visit(AstScopeName* nodep) override {
        // For use under AstCCalls for dpiImports.  ScopeNames under
        // displays are handled in AstDisplay
        if (!nodep->dpiExport()) {
            // this is where the DPI import context scope is set
            string scope = nodep->scopeDpiName();
            putbs("(&(vlSymsp->" + protect("__Vscope_" + scope) + "))");
        }
    }
    virtual void visit(AstSFormat* nodep) override {
        displayNode(nodep, nodep->fmtp()->scopeNamep(), nodep->fmtp()->text(),
                    nodep->fmtp()->exprsp(), false);
    }
    virtual void visit(AstSFormatF* nodep) override {
        displayNode(nodep, nodep->scopeNamep(), nodep->text(), nodep->exprsp(), false);
    }
    virtual void visit(AstFScanF* nodep) override {
        displayNode(nodep, nullptr, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstSScanF* nodep) override {
        displayNode(nodep, nullptr, nodep->text(), nodep->exprsp(), true);
    }
    virtual void visit(AstValuePlusArgs* nodep) override {
        puts("VL_VALUEPLUSARGS_IN");
        emitIQW(nodep->outp());
        puts("(");
        puts(cvtToStr(nodep->outp()->widthMin()));
        puts(", ");
        emitCvtPackStr(nodep->searchp());
        puts(", ");
        putbs("");
        iterateAndNextNull(nodep->outp());
        puts(")");
    }
    virtual void visit(AstTestPlusArgs* nodep) override {
        puts("VL_TESTPLUSARGS_I(");
        putsQuoted(nodep->text());
        puts(")");
    }
    virtual void visit(AstFError* nodep) override {
        puts("VL_FERROR_IN(");
        iterateAndNextNull(nodep->filep());
        putbs(", ");
        iterateAndNextNull(nodep->strp());
        puts(")");
    }
    virtual void visit(AstFGetS* nodep) override {
        checkMaxWords(nodep);
        emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nullptr);
    }

    void checkMaxWords(AstNode* nodep) {
        if (nodep->widthWords() > VL_TO_STRING_MAX_WORDS) {
            nodep->v3error(
                "String of "
                << nodep->width()
                << " bits exceeds hardcoded limit VL_TO_STRING_MAX_WORDS in verilatedos.h");
        }
    }
    virtual void visit(AstFOpen* nodep) override {
        iterateAndNextNull(nodep->filep());
        puts(" = VL_FOPEN_NN(");
        emitCvtPackStr(nodep->filenamep());
        putbs(", ");
        if (nodep->modep()->width() > 4 * 8)
            nodep->modep()->v3error("$fopen mode should be <= 4 characters");
        emitCvtPackStr(nodep->modep());
        puts(");\n");
    }
    virtual void visit(AstFOpenMcd* nodep) override {
        iterateAndNextNull(nodep->filep());
        puts(" = VL_FOPEN_MCD_N(");
        emitCvtPackStr(nodep->filenamep());
        puts(");\n");
    }
    virtual void visit(AstNodeReadWriteMem* nodep) override {
        puts(nodep->cFuncPrefixp());
        puts("N(");
        puts(nodep->isHex() ? "true" : "false");
        putbs(", ");
        // Need real storage width
        puts(cvtToStr(nodep->memp()->dtypep()->subDTypep()->widthMin()));
        uint32_t array_lo = 0;
        {
            const AstVarRef* varrefp = VN_CAST(nodep->memp(), VarRef);
            if (!varrefp) {
                nodep->v3error(nodep->verilogKwd() << " loading non-variable");
            } else if (VN_IS(varrefp->varp()->dtypeSkipRefp(), AssocArrayDType)) {
                // nodep->memp() below will when verilated code is compiled create a C++ template
            } else if (const AstUnpackArrayDType* adtypep
                       = VN_CAST(varrefp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                putbs(", ");
                puts(cvtToStr(varrefp->varp()->dtypep()->arrayUnpackedElements()));
                array_lo = adtypep->lo();
                putbs(", ");
                puts(cvtToStr(array_lo));
            } else {
                nodep->v3error(nodep->verilogKwd()
                               << " loading other than unpacked/associative-array variable");
            }
        }
        putbs(", ");
        emitCvtPackStr(nodep->filenamep());
        putbs(", ");
        {
            const bool need_ptr = !VN_IS(nodep->memp()->dtypep(), AssocArrayDType);
            if (need_ptr) puts(" &(");
            iterateAndNextNull(nodep->memp());
            if (need_ptr) puts(")");
        }
        putbs(", ");
        if (nodep->lsbp()) {
            iterateAndNextNull(nodep->lsbp());
        } else {
            puts(cvtToStr(array_lo));
        }
        putbs(", ");
        if (nodep->msbp()) {
            iterateAndNextNull(nodep->msbp());
        } else {
            puts("~0ULL");
        }
        puts(");\n");
    }
    virtual void visit(AstFClose* nodep) override {
        puts("VL_FCLOSE_I(");
        iterateAndNextNull(nodep->filep());
        puts("); ");
        iterateAndNextNull(nodep->filep());  // For safety, so user doesn't later WRITE with it.
        puts(" = 0;\n");
    }
    virtual void visit(AstFFlush* nodep) override {
        if (!nodep->filep()) {
            puts("Verilated::runFlushCallbacks();\n");
        } else {
            puts("if (");
            iterateAndNextNull(nodep->filep());
            puts(") { VL_FFLUSH_I(");
            iterateAndNextNull(nodep->filep());
            puts("); }\n");
        }
    }
    virtual void visit(AstFSeek* nodep) override {
        puts("(VL_FSEEK_I(");
        iterateAndNextNull(nodep->filep());
        puts(",");
        iterateAndNextNull(nodep->offset());
        puts(",");
        iterateAndNextNull(nodep->operation());
        puts(") == -1 ? -1 : 0)");
    }
    virtual void visit(AstFTell* nodep) override {
        puts("VL_FTELL_I(");
        iterateAndNextNull(nodep->filep());
        puts(")");
    }
    virtual void visit(AstFRewind* nodep) override {
        puts("(VL_FSEEK_I(");
        iterateAndNextNull(nodep->filep());
        puts(", 0, 0) == -1 ? -1 : 0)");
    }
    virtual void visit(AstFRead* nodep) override {
        puts("VL_FREAD_I(");
        puts(cvtToStr(nodep->memp()->widthMin()));  // Need real storage width
        putbs(",");
        uint32_t array_lo = 0;
        uint32_t array_size = 0;
        {
            const AstVarRef* varrefp = VN_CAST(nodep->memp(), VarRef);
            if (!varrefp) {
                nodep->v3error(nodep->verilogKwd() << " loading non-variable");
            } else if (VN_CAST(varrefp->varp()->dtypeSkipRefp(), BasicDType)) {
            } else if (const AstUnpackArrayDType* adtypep
                       = VN_CAST(varrefp->varp()->dtypeSkipRefp(), UnpackArrayDType)) {
                array_lo = adtypep->lo();
                array_size = adtypep->elementsConst();
            } else {
                nodep->v3error(nodep->verilogKwd()
                               << " loading other than unpacked-array variable");
            }
        }
        puts(cvtToStr(array_lo));
        putbs(",");
        puts(cvtToStr(array_size));
        putbs(", ");
        puts("&(");
        iterateAndNextNull(nodep->memp());
        puts(")");
        putbs(", ");
        iterateAndNextNull(nodep->filep());
        putbs(", ");
        if (nodep->startp()) {
            iterateAndNextNull(nodep->startp());
        } else {
            puts(cvtToStr(array_lo));
        }
        putbs(", ");
        if (nodep->countp()) {
            iterateAndNextNull(nodep->countp());
        } else {
            puts(cvtToStr(array_size));
        }
        puts(")");
    }
    virtual void visit(AstSysFuncAsTask* nodep) override {
        if (!nodep->lhsp()->isWide()) puts("(void)");
        iterateAndNextNull(nodep->lhsp());
        if (!nodep->lhsp()->isWide()) puts(";");
    }
    virtual void visit(AstSystemT* nodep) override {
        puts("(void)VL_SYSTEM_I");
        emitIQW(nodep->lhsp());
        puts("(");
        if (nodep->lhsp()->isWide()) {
            puts(cvtToStr(nodep->lhsp()->widthWords()));
            putbs(", ");
        }
        checkMaxWords(nodep->lhsp());
        iterateAndNextNull(nodep->lhsp());
        puts(");\n");
    }
    virtual void visit(AstSystemF* nodep) override {
        puts("VL_SYSTEM_I");
        emitIQW(nodep->lhsp());
        puts("(");
        if (nodep->lhsp()->isWide()) {
            puts(cvtToStr(nodep->lhsp()->widthWords()));
            putbs(", ");
        }
        checkMaxWords(nodep->lhsp());
        iterateAndNextNull(nodep->lhsp());
        puts(")");
    }
    virtual void visit(AstJumpBlock* nodep) override {
        nodep->labelNum(++m_labelNum);
        puts("{\n");  // Make it visually obvious label jumps outside these
        iterateAndNextNull(nodep->stmtsp());
        iterateAndNextNull(nodep->endStmtsp());
        puts("}\n");
    }
    virtual void visit(AstJumpGo* nodep) override {
        puts("goto __Vlabel" + cvtToStr(nodep->labelp()->blockp()->labelNum()) + ";\n");
    }
    virtual void visit(AstJumpLabel* nodep) override {
        puts("__Vlabel" + cvtToStr(nodep->blockp()->labelNum()) + ": ;\n");
    }
    virtual void visit(AstWhile* nodep) override {
        iterateAndNextNull(nodep->precondsp());
        puts("while (");
        iterateAndNextNull(nodep->condp());
        puts(") {\n");
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        iterateAndNextNull(nodep->precondsp());  // Need to recompute before next loop
        puts("}\n");
    }
    virtual void visit(AstNodeIf* nodep) override {
        puts("if (");
        if (!nodep->branchPred().unknown()) {
            puts(nodep->branchPred().ascii());
            puts("(");
        }
        iterateAndNextNull(nodep->condp());
        if (!nodep->branchPred().unknown()) puts(")");
        puts(") {\n");
        iterateAndNextNull(nodep->ifsp());
        puts("}");
        if (!nodep->elsesp()) {
            puts("\n");
        } else {
            if (VN_IS(nodep->elsesp(), NodeIf) && !nodep->elsesp()->nextp()) {
                puts(" else ");
                iterateAndNextNull(nodep->elsesp());
            } else {
                puts(" else {\n");
                iterateAndNextNull(nodep->elsesp());
                puts("}\n");
            }
        }
    }
    virtual void visit(AstExprStmt* nodep) override {
        // GCC allows compound statements in expressions, but this is not standard.
        // So we use an immediate-evaluation lambda and comma operator
        putbs("([&]() {\n");
        iterateAndNextNull(nodep->stmtsp());
        puts("}(), ");
        iterateAndNextNull(nodep->resultp());
        puts(")");
    }
    virtual void visit(AstStop* nodep) override {
        puts("VL_STOP_MT(");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(", \"\"");
        puts(");\n");
    }
    virtual void visit(AstFinish* nodep) override {
        puts("VL_FINISH_MT(");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(", \"\");\n");
    }
    virtual void visit(AstPrintTimeScale* nodep) override {
        puts("VL_PRINTTIMESCALE(");
        putsQuoted(protect(nodep->name()));
        puts(", ");
        putsQuoted(nodep->timeunit().ascii());
        puts(", vlSymsp->_vm_contextp__);\n");
    }
    virtual void visit(AstRand* nodep) override {
        emitOpName(nodep, nodep->emitC(), nodep->seedp(), nullptr, nullptr);
    }
    virtual void visit(AstTime* nodep) override {
        puts("VL_TIME_UNITED_Q(");
        if (nodep->timeunit().isNone()) nodep->v3fatalSrc("$time has no units");
        puts(cvtToStr(nodep->timeunit().multiplier()
                      / v3Global.rootp()->timeprecision().multiplier()));
        puts(")");
    }
    virtual void visit(AstTimeD* nodep) override {
        puts("VL_TIME_UNITED_D(");
        if (nodep->timeunit().isNone()) nodep->v3fatalSrc("$realtime has no units");
        puts(cvtToStr(nodep->timeunit().multiplier()
                      / v3Global.rootp()->timeprecision().multiplier()));
        puts(")");
    }
    virtual void visit(AstTimeFormat* nodep) override {
        puts("VL_TIMEFORMAT_IINI(");
        iterateAndNextNull(nodep->unitsp());
        puts(", ");
        iterateAndNextNull(nodep->precisionp());
        puts(", ");
        emitCvtPackStr(nodep->suffixp());
        puts(", ");
        iterateAndNextNull(nodep->widthp());
        puts(", vlSymsp->_vm_contextp__);\n");
    }
    virtual void visit(AstNodeSimpleText* nodep) override {
        if (nodep->tracking() || m_trackText) {
            puts(nodep->text());
        } else {
            ofp()->putsNoTracking(nodep->text());
        }
    }
    virtual void visit(AstTextBlock* nodep) override {
        visit(VN_CAST(nodep, NodeSimpleText));
        for (AstNode* childp = nodep->nodesp(); childp; childp = childp->nextp()) {
            iterate(childp);
            if (nodep->commas() && childp->nextp()) puts(", ");
        }
    }
    virtual void visit(AstCStmt* nodep) override {
        putbs("");
        iterateAndNextNull(nodep->bodysp());
    }
    virtual void visit(AstCMath* nodep) override {
        putbs("");
        iterateAndNextNull(nodep->bodysp());
    }
    virtual void visit(AstUCStmt* nodep) override {
        putsDecoration(ifNoProtect("// $c statement at " + nodep->fileline()->ascii() + "\n"));
        iterateAndNextNull(nodep->bodysp());
        puts("\n");
    }
    virtual void visit(AstUCFunc* nodep) override {
        puts("\n");
        putsDecoration(ifNoProtect("// $c function at " + nodep->fileline()->ascii() + "\n"));
        iterateAndNextNull(nodep->bodysp());
        puts("\n");
    }

    // Operators
    virtual void visit(AstNodeTermop* nodep) override {
        emitOpName(nodep, nodep->emitC(), nullptr, nullptr, nullptr);
    }
    virtual void visit(AstNodeUniop* nodep) override {
        if (nodep->emitCheckMaxWords()
            && (nodep->widthWords() > VL_MULS_MAX_WORDS
                || nodep->lhsp()->widthWords() > VL_MULS_MAX_WORDS)) {
            nodep->v3warn(
                E_UNSUPPORTED,
                "Unsupported: "
                    << nodep->prettyOperatorName() << " operator of " << nodep->width()
                    << " bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
        }
        if (emitSimpleOk(nodep)) {
            putbs("(");
            puts(nodep->emitSimpleOperator());
            puts(" ");
            iterateAndNextNull(nodep->lhsp());
            puts(")");
        } else {
            emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nullptr, nullptr);
        }
    }
    virtual void visit(AstNodeBiop* nodep) override {
        if (nodep->emitCheckMaxWords() && nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3warn(
                E_UNSUPPORTED,
                "Unsupported: "
                    << nodep->prettyOperatorName() << " operator of " << nodep->width()
                    << " bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
        }
        if (emitSimpleOk(nodep)) {
            putbs("(");
            iterateAndNextNull(nodep->lhsp());
            puts(" ");
            putbs(nodep->emitSimpleOperator());
            puts(" ");
            iterateAndNextNull(nodep->rhsp());
            puts(")");
        } else {
            emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nullptr);
        }
    }
    virtual void visit(AstNodeTriop* nodep) override {
        UASSERT_OBJ(!emitSimpleOk(nodep), nodep, "Triop cannot be described in a simple way");
        emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nodep->thsp());
    }
    virtual void visit(AstRedXor* nodep) override {
        if (nodep->lhsp()->isWide()) {
            visit(VN_CAST(nodep, NodeUniop));
        } else {
            putbs("VL_REDXOR_");
            puts(cvtToStr(nodep->lhsp()->dtypep()->widthPow2()));
            puts("(");
            iterateAndNextNull(nodep->lhsp());
            puts(")");
        }
    }
    virtual void visit(AstCCast* nodep) override {
        // Extending a value of the same word width is just a NOP.
        if (nodep->size() <= VL_IDATASIZE) {
            puts("(IData)(");
        } else {
            puts("(QData)(");
        }
        iterateAndNextNull(nodep->lhsp());
        puts(")");
    }
    virtual void visit(AstNodeCond* nodep) override {
        // Widths match up already, so we'll just use C++'s operator w/o any temps.
        if (nodep->expr1p()->isWide()) {
            emitOpName(nodep, nodep->emitC(), nodep->condp(), nodep->expr1p(), nodep->expr2p());
        } else {
            putbs("(");
            iterateAndNextNull(nodep->condp());
            putbs(" ? ");
            iterateAndNextNull(nodep->expr1p());
            putbs(" : ");
            iterateAndNextNull(nodep->expr2p());
            puts(")");
        }
    }
    virtual void visit(AstMemberSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        putbs("->");
        puts(nodep->varp()->nameProtect());
    }
    virtual void visit(AstNullCheck* nodep) override {
        puts("VL_NULL_CHECK(");
        iterateAndNextNull(nodep->lhsp());
        puts(", ");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(")");
    }
    virtual void visit(AstCNew* nodep) override {
        puts("std::make_shared<" + prefixNameProtect(nodep->dtypep()) + ">(");
        puts("vlSymsp");  // TODO make this part of argsp, and eliminate when unnecessary
        if (nodep->argsp()) puts(", ");
        iterateAndNextNull(nodep->argsp());
        puts(")");
    }
    virtual void visit(AstNewCopy* nodep) override {
        puts("std::make_shared<" + prefixNameProtect(nodep->dtypep()) + ">(");
        puts("*");  // i.e. make into a reference
        iterateAndNextNull(nodep->rhsp());
        puts(")");
    }
    virtual void visit(AstSel* nodep) override {
        // Note ASSIGN checks for this on a LHS
        emitOpName(nodep, nodep->emitC(), nodep->fromp(), nodep->lsbp(), nodep->thsp());
    }
    virtual void visit(AstReplicate* nodep) override {
        if (nodep->lhsp()->widthMin() == 1 && !nodep->isWide()) {
            UASSERT_OBJ((static_cast<int>(VN_CAST(nodep->rhsp(), Const)->toUInt())
                         * nodep->lhsp()->widthMin())
                            == nodep->widthMin(),
                        nodep, "Replicate non-constant or width miscomputed");
            puts("VL_REPLICATE_");
            emitIQW(nodep);
            puts("OI(");
            puts(cvtToStr(nodep->widthMin()));
            if (nodep->lhsp()) puts("," + cvtToStr(nodep->lhsp()->widthMin()));
            if (nodep->rhsp()) puts("," + cvtToStr(nodep->rhsp()->widthMin()));
            puts(",");
            iterateAndNextNull(nodep->lhsp());
            puts(", ");
            iterateAndNextNull(nodep->rhsp());
            puts(")");
        } else {
            emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nullptr);
        }
    }
    virtual void visit(AstStreamL* nodep) override {
        // Attempt to use a "fast" stream function for slice size = power of 2
        if (!nodep->isWide()) {
            uint32_t isPow2 = VN_CAST(nodep->rhsp(), Const)->num().countOnes() == 1;
            uint32_t sliceSize = VN_CAST(nodep->rhsp(), Const)->toUInt();
            if (isPow2 && sliceSize <= (nodep->isQuad() ? sizeof(uint64_t) : sizeof(uint32_t))) {
                puts("VL_STREAML_FAST_");
                emitIQW(nodep);
                emitIQW(nodep->lhsp());
                puts("I(");
                puts(cvtToStr(nodep->widthMin()));
                puts("," + cvtToStr(nodep->lhsp()->widthMin()));
                puts("," + cvtToStr(nodep->rhsp()->widthMin()));
                puts(",");
                iterateAndNextNull(nodep->lhsp());
                puts(", ");
                uint32_t rd_log2 = V3Number::log2b(VN_CAST(nodep->rhsp(), Const)->toUInt());
                puts(cvtToStr(rd_log2) + ")");
                return;
            }
        }
        emitOpName(nodep, "VL_STREAML_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)", nodep->lhsp(),
                   nodep->rhsp(), nullptr);
    }
    virtual void visit(AstCastDynamic* nodep) override {
        putbs("VL_CAST_DYNAMIC(");
        iterateAndNextNull(nodep->lhsp());
        puts(", ");
        iterateAndNextNull(nodep->rhsp());
        puts(")");
    }
    virtual void visit(AstCountBits* nodep) override {
        putbs("VL_COUNTBITS_");
        emitIQW(nodep->lhsp());
        puts("(");
        puts(cvtToStr(nodep->lhsp()->widthMin()));
        puts(", ");
        if (nodep->lhsp()->isWide()) {
            puts(cvtToStr(nodep->lhsp()->widthWords()));  // Note argument width, not node width
                                                          // (which is always 32)
            puts(", ");
        }
        iterateAndNextNull(nodep->lhsp());
        puts(", ");
        iterateAndNextNull(nodep->rhsp());
        puts(", ");
        iterateAndNextNull(nodep->thsp());
        puts(", ");
        iterateAndNextNull(nodep->fhsp());
        puts(")");
    }
    virtual void visit(AstInitItem* nodep) override { iterateChildren(nodep); }
    // Terminals
    virtual void visit(AstVarRef* nodep) override {
        puts(nodep->hiernameProtect());
        puts(nodep->varp()->nameProtect());
    }
    void emitCvtPackStr(AstNode* nodep) {
        if (const AstConst* constp = VN_CAST(nodep, Const)) {
            putbs("std::string(");
            putsQuoted(constp->num().toString());
            puts(")");
        } else {
            putbs("VL_CVT_PACK_STR_N");
            emitIQW(nodep);
            puts("(");
            if (nodep->isWide()) {
                // Note argument width, not node width (which is always 32)
                puts(cvtToStr(nodep->widthWords()));
                puts(", ");
            }
            iterateAndNextNull(nodep);
            puts(")");
        }
    }
    void emitCvtWideArray(AstNode* nodep, AstNode* fromp) {
        putbs("VL_CVT_W_A(");
        iterate(nodep);
        puts(", ");
        iterate(fromp);
        putbs(".atDefault()");  // Not accessed; only to get the proper type of values
        puts(")");
    }
    void emitConstant(AstConst* nodep, AstVarRef* assigntop, const string& assignString) {
        // Put out constant set to the specified variable, or given variable in a string
        if (nodep->num().isFourState()) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: 4-state numbers in this context");
        } else if (nodep->num().isString()) {
            putbs("std::string(");
            putsQuoted(nodep->num().toString());
            puts(")");
        } else if (nodep->isWide()) {
            int upWidth = nodep->num().widthMin();
            int chunks = 0;
            if (upWidth > EMITC_NUM_CONSTW * VL_EDATASIZE) {
                // Output e.g. 8 words in groups of e.g. 8
                chunks = (upWidth - 1) / (EMITC_NUM_CONSTW * VL_EDATASIZE);
                upWidth %= (EMITC_NUM_CONSTW * VL_EDATASIZE);
                if (upWidth == 0) upWidth = (EMITC_NUM_CONSTW * VL_EDATASIZE);
            }
            {  // Upper e.g. 8 words
                if (chunks) {
                    putbs("VL_CONSTHI_W_");
                    puts(cvtToStr(VL_WORDS_I(upWidth)));
                    puts("X(");
                    puts(cvtToStr(nodep->widthMin()));
                    puts(",");
                    puts(cvtToStr(chunks * EMITC_NUM_CONSTW * VL_EDATASIZE));
                } else {
                    putbs("VL_CONST_W_");
                    puts(cvtToStr(VL_WORDS_I(upWidth)));
                    puts("X(");
                    puts(cvtToStr(nodep->widthMin()));
                }
                puts(",");
                if (!assigntop) {
                    puts(assignString);
                } else if (VN_IS(assigntop, VarRef)) {
                    puts(assigntop->hiernameProtect());
                    puts(assigntop->varp()->nameProtect());
                } else {
                    iterateAndNextNull(assigntop);
                }
                for (int word = VL_WORDS_I(upWidth) - 1; word >= 0; word--) {
                    // Only 32 bits - llx + long long here just to appease CPP format warning
                    ofp()->printf(",0x%08" VL_PRI64 "x",
                                  static_cast<vluint64_t>(
                                      nodep->num().edataWord(word + chunks * EMITC_NUM_CONSTW)));
                }
                puts(")");
            }
            for (chunks--; chunks >= 0; chunks--) {
                puts(";\n");
                putbs("VL_CONSTLO_W_");
                puts(cvtToStr(EMITC_NUM_CONSTW));
                puts("X(");
                puts(cvtToStr(chunks * EMITC_NUM_CONSTW * VL_EDATASIZE));
                puts(",");
                if (!assigntop) {
                    puts(assignString);
                } else if (VN_IS(assigntop, VarRef)) {
                    puts(assigntop->hiernameProtect());
                    puts(assigntop->varp()->nameProtect());
                } else {
                    iterateAndNextNull(assigntop);
                }
                for (int word = EMITC_NUM_CONSTW - 1; word >= 0; word--) {
                    // Only 32 bits - llx + long long here just to appease CPP format warning
                    ofp()->printf(",0x%08" VL_PRI64 "x",
                                  static_cast<vluint64_t>(
                                      nodep->num().edataWord(word + chunks * EMITC_NUM_CONSTW)));
                }
                puts(")");
            }
        } else if (nodep->isDouble()) {
            if (int(nodep->num().toDouble()) == nodep->num().toDouble()
                && nodep->num().toDouble() < 1000 && nodep->num().toDouble() > -1000) {
                ofp()->printf("%3.1f", nodep->num().toDouble());  // Force decimal point
            } else {
                // Not %g as will not always put in decimal point, so not obvious to compiler
                // is a real number
                ofp()->printf("%.17e", nodep->num().toDouble());
            }
        } else if (nodep->isQuad()) {
            vluint64_t num = nodep->toUQuad();
            if (num < 10) {
                ofp()->printf("%" VL_PRI64 "uULL", num);
            } else {
                ofp()->printf("0x%" VL_PRI64 "xULL", num);
            }
        } else {
            uint32_t num = nodep->toUInt();
            // Only 32 bits - llx + long long here just to appease CPP format warning
            if (num < 10) {
                puts(cvtToStr(num));
            } else {
                ofp()->printf("0x%" VL_PRI64 "x", static_cast<vluint64_t>(num));
            }
            // If signed, we'll do our own functions
            // But must be here, or <= comparisons etc may end up signed
            puts("U");
        }
    }
    void emitSetVarConstant(const string& assignString, AstConst* constp) {
        if (!constp->isWide()) {
            puts(assignString);
            puts(" = ");
        }
        emitConstant(constp, nullptr, assignString);
        puts(";\n");
    }
    virtual void visit(AstConst* nodep) override {
        if (nodep->isWide()) {
            UASSERT_OBJ(m_wideTempRefp, nodep, "Wide Constant w/ no temp");
            emitConstant(nodep, m_wideTempRefp, "");
            m_wideTempRefp = nullptr;  // We used it, barf if set it a second time
        } else {
            emitConstant(nodep, nullptr, "");
        }
    }

    // Just iterate
    virtual void visit(AstNetlist* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstTopScope* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstScope* nodep) override { iterateChildren(nodep); }
    // NOPs
    virtual void visit(AstTypedef*) override {}
    virtual void visit(AstPragma*) override {}
    virtual void visit(AstCell*) override {}  // Handled outside the Visit class
    virtual void visit(AstVar*) override {}  // Handled outside the Visit class
    virtual void visit(AstNodeText*) override {}  // Handled outside the Visit class
    virtual void visit(AstTraceDecl*) override {}  // Handled outside the Visit class
    virtual void visit(AstTraceInc*) override {}  // Handled outside the Visit class
    virtual void visit(AstCFile*) override {}  // Handled outside the Visit class
    virtual void visit(AstCellInline*) override {}  // Handled outside visit (in EmitCSyms)
    virtual void visit(AstCUse*) override {}  // Handled outside the Visit class
    // Default
    virtual void visit(AstNode* nodep) override {
        puts(string("\n???? // ") + nodep->prettyTypeName() + "\n");
        iterateChildren(nodep);
        if (!v3Global.opt.lintOnly()) {  // An internal problem, so suppress
            nodep->v3fatalSrc("Unknown node type reached emitter: " << nodep->prettyTypeName());
        }
    }

    EmitCStmts() {
        m_suppressSemi = false;
        m_wideTempRefp = nullptr;
        m_labelNum = 0;
        m_splitSize = 0;
        m_splitFilenum = 0;
    }
    EmitCStmts(AstNode* nodep, V3OutCFile* ofp, bool trackText = false)
        : EmitCStmts{} {
        m_ofp = ofp;
        m_trackText = trackText;
        iterate(nodep);
    }
    virtual ~EmitCStmts() override = default;
};

//######################################################################
// Establish mtask variable sort order in mtasks mode

class EmitVarTspSorter final : public V3TSP::TspStateBase {
private:
    // MEMBERS
    const MTaskIdSet& m_mtaskIds;  // Mtask we're ordering
    static unsigned s_serialNext;  // Unique ID to establish serial order
    unsigned m_serial;  // Serial ordering
public:
    // CONSTRUCTORS
    explicit EmitVarTspSorter(const MTaskIdSet& mtaskIds)
        : m_mtaskIds(mtaskIds) {  // Cannot be {} or GCC 4.8 false warning
        m_serial = ++s_serialNext;  // Cannot be ()/{} or GCC 4.8 false warning
    }
    virtual ~EmitVarTspSorter() = default;
    // METHODS
    virtual bool operator<(const TspStateBase& other) const override {
        return operator<(dynamic_cast<const EmitVarTspSorter&>(other));
    }
    bool operator<(const EmitVarTspSorter& other) const { return m_serial < other.m_serial; }
    const MTaskIdSet& mtaskIds() const { return m_mtaskIds; }
    virtual int cost(const TspStateBase* otherp) const override {
        return cost(dynamic_cast<const EmitVarTspSorter*>(otherp));
    }
    virtual int cost(const EmitVarTspSorter* otherp) const {
        int cost = diffs(m_mtaskIds, otherp->m_mtaskIds);
        cost += diffs(otherp->m_mtaskIds, m_mtaskIds);
        return cost;
    }
    // Returns the number of elements in set_a that don't appear in set_b
    static int diffs(const MTaskIdSet& set_a, const MTaskIdSet& set_b) {
        int diffs = 0;
        for (int i : set_a) {
            if (set_b.find(i) == set_b.end()) ++diffs;
        }
        return diffs;
    }
};

unsigned EmitVarTspSorter::s_serialNext = 0;

//######################################################################
// Internal EmitC implementation

class EmitCImp final : EmitCStmts {
    // MEMBERS
    AstNodeModule* m_modp = nullptr;
    AstNodeModule* m_fileModp = nullptr;  // Files (names, headers) constructed using this module
    std::vector<AstChangeDet*> m_blkChangeDetVec;  // All encountered changes in block
    bool m_slow = false;  // Creating __Slow file
    bool m_fast = false;  // Creating non __Slow file (or both)

    //---------------------------------------
    // METHODS

    void doubleOrDetect(AstChangeDet* changep, bool& gotOne) {
        // cppcheck-suppress variableScope
        static int s_addDoubleOr = 10;  // Determined experimentally as best
        if (!changep->rhsp()) {
            if (!gotOne) {
                gotOne = true;
            } else {
                puts(" | ");
            }
            iterateAndNextNull(changep->lhsp());
        } else {
            AstNode* lhsp = changep->lhsp();
            AstNode* rhsp = changep->rhsp();
            UASSERT_OBJ(VN_IS(lhsp, VarRef) || VN_IS(lhsp, ArraySel), changep, "Not ref?");
            UASSERT_OBJ(VN_IS(rhsp, VarRef) || VN_IS(rhsp, ArraySel), changep, "Not ref?");
            for (int word = 0;
                 word < (changep->lhsp()->isWide() ? changep->lhsp()->widthWords() : 1); ++word) {
                if (!gotOne) {
                    gotOne = true;
                    s_addDoubleOr = 10;
                    puts("(");
                } else if (--s_addDoubleOr == 0) {
                    puts("|| (");
                    s_addDoubleOr = 10;
                } else {
                    puts(" | (");
                }
                iterateAndNextNull(changep->lhsp());
                if (changep->lhsp()->isWide()) puts("[" + cvtToStr(word) + "]");
                if (changep->lhsp()->isDouble()) {
                    puts(" != ");
                } else {
                    puts(" ^ ");
                }
                iterateAndNextNull(changep->rhsp());
                if (changep->lhsp()->isWide()) puts("[" + cvtToStr(word) + "]");
                puts(")");
            }
        }
    }

    V3OutCFile* newOutCFile(bool slow, bool source, int filenum = 0) {
        string filenameNoExt = v3Global.opt.makeDir() + "/" + prefixNameProtect(m_fileModp);
        if (filenum) filenameNoExt += "__" + cvtToStr(filenum);
        filenameNoExt += (slow ? "__Slow" : "");
        V3OutCFile* ofp = nullptr;
        if (v3Global.opt.lintOnly()) {
            // Unfortunately we have some lint checks here, so we can't just skip processing.
            // We should move them to a different stage.
            string filename = VL_DEV_NULL;
            newCFile(filename, slow, source);
            ofp = new V3OutCFile(filename);
        } else if (optSystemC()) {
            string filename = filenameNoExt + (source ? ".cpp" : ".h");
            newCFile(filename, slow, source);
            ofp = new V3OutScFile(filename);
        } else {
            string filename = filenameNoExt + (source ? ".cpp" : ".h");
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

    // Returns the number of cross-thread dependencies into mtaskp.
    // If >0, mtaskp must test whether its prereqs are done before starting,
    // and may need to block.
    static uint32_t packedMTaskMayBlock(const ExecMTask* mtaskp) {
        uint32_t result = 0;
        for (V3GraphEdge* edgep = mtaskp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            const ExecMTask* prevp = dynamic_cast<ExecMTask*>(edgep->fromp());
            if (prevp->thread() != mtaskp->thread()) ++result;
        }
        return result;
    }

    void emitMTaskBody(AstMTaskBody* nodep) {
        ExecMTask* curExecMTaskp = nodep->execMTaskp();
        if (packedMTaskMayBlock(curExecMTaskp)) {
            puts("vlTOPp->__Vm_mt_" + cvtToStr(curExecMTaskp->id())
                 + ".waitUntilUpstreamDone(even_cycle);\n");
        }

        string recName;
        if (v3Global.opt.profThreads()) {
            recName = "__Vprfthr_" + cvtToStr(curExecMTaskp->id());
            puts("VlProfileRec* " + recName + " = nullptr;\n");
            // Leave this if() here, as don't want to call VL_RDTSC_Q unless profiling
            puts("if (VL_UNLIKELY(vlTOPp->__Vm_profile_cycle_start)) {\n");
            puts(recName + " = vlTOPp->__Vm_threadPoolp->profileAppend();\n");
            puts(recName + "->startRecord(VL_RDTSC_Q() - vlTOPp->__Vm_profile_cycle_start,");
            puts(" " + cvtToStr(curExecMTaskp->id()) + ",");
            puts(" " + cvtToStr(curExecMTaskp->cost()) + ");\n");
            puts("}\n");
        }
        puts("Verilated::mtaskId(" + cvtToStr(curExecMTaskp->id()) + ");\n");

        // The actual body of calls to leaf functions
        iterateAndNextNull(nodep->stmtsp());

        if (v3Global.opt.profThreads()) {
            // Leave this if() here, as don't want to call VL_RDTSC_Q unless profiling
            puts("if (VL_UNLIKELY(" + recName + ")) {\n");
            puts(recName + "->endRecord(VL_RDTSC_Q() - vlTOPp->__Vm_profile_cycle_start);\n");
            puts("}\n");
        }

        // Flush message queue
        puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");

        // For any downstream mtask that's on another thread, bump its
        // counter and maybe notify it.
        for (V3GraphEdge* edgep = curExecMTaskp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            const ExecMTask* nextp = dynamic_cast<ExecMTask*>(edgep->top());
            if (nextp->thread() != curExecMTaskp->thread()) {
                puts("vlTOPp->__Vm_mt_" + cvtToStr(nextp->id())
                     + ".signalUpstreamDone(even_cycle);\n");
            }
        }

        // Run the next mtask inline
        const ExecMTask* nextp = curExecMTaskp->packNextp();
        if (nextp) {
            emitMTaskBody(nextp->bodyp());
        } else {
            // Unblock the fake "final" mtask
            puts("vlTOPp->__Vm_mt_final.signalUpstreamDone(even_cycle);\n");
        }
    }

    virtual void visit(AstMTaskBody* nodep) override {
        maybeSplit();
        splitSizeInc(10);

        const ExecMTask* const mtp = nodep->execMTaskp();
        puts("\n");
        puts("void ");
        puts(prefixNameProtect(m_modp) + "::" + protect(mtp->cFuncName()));
        puts("(bool even_cycle, void* symtab) {\n");

        // Declare and set vlSymsp
        puts(EmitCBaseVisitor::symClassVar() + " = (" + EmitCBaseVisitor::symClassName()
             + "*)symtab;\n");
        puts(EmitCBaseVisitor::symTopAssign() + "\n");

        emitMTaskBody(nodep);
        puts("}\n");
    }

    //---------------------------------------
    // VISITORS
    using EmitCStmts::visit;  // Suppress hidden overloaded virtual function warning
    virtual void visit(AstCFunc* nodep) override {
        // TRACE_* and DPI handled elsewhere
        if (nodep->funcType().isTrace()) return;
        if (nodep->dpiImport()) return;
        if (!(nodep->slow() ? m_slow : m_fast)) return;

        maybeSplit();

        m_blkChangeDetVec.clear();

        splitSizeInc(nodep);

        puts("\n");
        if (nodep->ifdef() != "") puts("#ifdef " + nodep->ifdef() + "\n");
        if (nodep->isInline()) puts("VL_INLINE_OPT ");
        if (!nodep->isConstructor() && !nodep->isDestructor()) {
            puts(nodep->rtnTypeVoid());
            puts(" ");
        }

        if (nodep->isMethod()) puts(prefixNameProtect(m_modp) + "::");
        puts(funcNameProtect(nodep, m_modp));
        puts("(" + cFuncArgs(nodep) + ")");
        if (nodep->isConst().trueKnown()) puts(" const");

        // TODO perhaps better to have a new AstCCtorInit so we can pass arguments
        // rather than requiring a string here
        if (!nodep->ctorInits().empty()) {
            puts(": ");
            puts(nodep->ctorInits());
        }
        puts(" {\n");

        // "+" in the debug indicates a print from the model
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+  ");
        for (int i = 0; i < m_modp->level(); ++i) { puts("  "); }
        puts(prefixNameProtect(m_modp) + "::" + nodep->nameProtect() + "\\n\"); );\n");

        // Declare and set vlTOPp
        if (nodep->symProlog()) puts(EmitCBaseVisitor::symTopAssign() + "\n");

        if (nodep->initsp()) putsDecoration("// Variables\n");
        for (AstNode* subnodep = nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* varp = VN_CAST(subnodep, Var)) {
                if (varp->isFuncReturn()) emitVarDecl(varp, "");
            }
        }
        string section;
        emitVarList(nodep->initsp(), EVL_FUNC_ALL, "", section /*ref*/);
        emitVarList(nodep->stmtsp(), EVL_FUNC_ALL, "", section /*ref*/);

        iterateAndNextNull(nodep->initsp());

        if (nodep->stmtsp()) putsDecoration("// Body\n");
        iterateAndNextNull(nodep->stmtsp());
        if (!m_blkChangeDetVec.empty()) emitChangeDet();

        if (nodep->finalsp()) putsDecoration("// Final\n");
        iterateAndNextNull(nodep->finalsp());
        //

        if (!m_blkChangeDetVec.empty()) puts("return __req;\n");

        // puts("__Vm_activity = true;\n");
        puts("}\n");
        if (nodep->ifdef() != "") puts("#endif  // " + nodep->ifdef() + "\n");
    }

    void emitChangeDet() {
        putsDecoration("// Change detection\n");
        puts("QData __req = false;  // Logically a bool\n");  // But not because it results in
                                                              // faster code
        bool gotOne = false;
        for (AstChangeDet* changep : m_blkChangeDetVec) {
            if (changep->lhsp()) {
                if (!gotOne) {  // Not a clocked block
                    puts("__req |= (");
                } else {
                    puts("\n");
                }
                doubleOrDetect(changep, gotOne);
            }
        }
        if (gotOne) puts(");\n");
        if (gotOne && !v3Global.opt.protectIds()) {
            // puts("VL_DEBUG_IF( if (__req) cout<<\"- CLOCKREQ );");
            for (AstChangeDet* nodep : m_blkChangeDetVec) {
                if (nodep->lhsp()) {
                    puts("VL_DEBUG_IF( if(__req && (");
                    bool gotOneIgnore = false;
                    doubleOrDetect(nodep, gotOneIgnore);
                    string varname;
                    if (VN_IS(nodep->lhsp(), VarRef)) {
                        varname = ": " + VN_CAST(nodep->lhsp(), VarRef)->varp()->prettyName();
                    }
                    puts(")) VL_DBG_MSGF(\"        CHANGE: ");
                    puts(protect(nodep->fileline()->filename()));
                    puts(":" + cvtToStr(nodep->fileline()->lineno()));
                    puts(varname + "\\n\"); );\n");
                }
            }
        }
    }

    virtual void visit(AstConsAssoc* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        puts("()");
        if (nodep->defaultp()) {
            putbs(".setDefault(");
            iterateAndNextNull(nodep->defaultp());
            puts(")");
        }
    }
    virtual void visit(AstSetAssoc* nodep) override {
        iterateAndNextNull(nodep->lhsp());
        putbs(".set(");
        iterateAndNextNull(nodep->keyp());
        puts(", ");
        putbs("");
        iterateAndNextNull(nodep->valuep());
        puts(")");
    }
    virtual void visit(AstConsDynArray* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        if (!nodep->lhsp()) {
            puts("()");
        } else {
            puts("::cons(");
            iterateAndNextNull(nodep->lhsp());
            if (nodep->rhsp()) {
                puts(", ");
                putbs("");
            }
            iterateAndNextNull(nodep->rhsp());
            puts(")");
        }
    }
    virtual void visit(AstConsQueue* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        if (!nodep->lhsp()) {
            puts("()");
        } else {
            puts("::cons(");
            iterateAndNextNull(nodep->lhsp());
            if (nodep->rhsp()) {
                puts(", ");
                putbs("");
            }
            iterateAndNextNull(nodep->rhsp());
            puts(")");
        }
    }

    virtual void visit(AstChangeDet* nodep) override {  //
        m_blkChangeDetVec.push_back(nodep);
    }

    virtual void visit(AstCReset* nodep) override {
        AstVar* varp = nodep->varrefp()->varp();
        emitVarReset(varp);
    }

    virtual void visit(AstExecGraph* nodep) override {
        UASSERT_OBJ(nodep == v3Global.rootp()->execGraphp(), nodep,
                    "ExecGraph should be a singleton!");
        // The location of the AstExecGraph within the containing _eval()
        // function is where we want to invoke the graph and wait for it to
        // complete. Do that now.
        //
        // Don't recurse to children -- this isn't the place to emit
        // function definitions for the nested CFuncs. We'll do that at the
        // end.
        puts("vlTOPp->__Vm_even_cycle = !vlTOPp->__Vm_even_cycle;\n");

        // Build the list of initial mtasks to start
        std::vector<const ExecMTask*> execMTasks;

        // Start each root mtask
        for (const V3GraphVertex* vxp = nodep->depGraphp()->verticesBeginp(); vxp;
             vxp = vxp->verticesNextp()) {
            const ExecMTask* etp = dynamic_cast<const ExecMTask*>(vxp);
            if (etp->threadRoot()) execMTasks.push_back(etp);
        }
        UASSERT_OBJ(execMTasks.size() <= static_cast<unsigned>(v3Global.opt.threads()), nodep,
                    "More root mtasks than available threads");

        if (!execMTasks.empty()) {
            for (uint32_t i = 0; i < execMTasks.size(); ++i) {
                bool runInline = (i == execMTasks.size() - 1);
                if (runInline) {
                    // The thread calling eval() will run this mtask inline,
                    // along with its packed successors.
                    puts(protect(execMTasks[i]->cFuncName())
                         + "(vlTOPp->__Vm_even_cycle, vlSymsp);\n");
                    puts("Verilated::mtaskId(0);\n");
                } else {
                    // The other N-1 go to the thread pool.
                    puts("vlTOPp->__Vm_threadPoolp->workerp(" + cvtToStr(i) + ")->addTask("
                         + protect(execMTasks[i]->cFuncName())
                         + ", vlTOPp->__Vm_even_cycle, vlSymsp);\n");
                }
            }
            puts("vlTOPp->__Vm_mt_final.waitUntilUpstreamDone(vlTOPp->__Vm_even_cycle);\n");
        }
    }

    //---------------------------------------
    // ACCESSORS

    // METHODS
    // Low level
    void emitModCUse(AstNodeModule* modp, VUseType useType) {
        string nl;
        for (AstNode* itemp = modp->stmtsp(); itemp; itemp = itemp->nextp()) {
            if (AstCUse* usep = VN_CAST(itemp, CUse)) {
                if (usep->useType() == useType) {
                    if (usep->useType().isInclude()) {
                        puts("#include \"" + prefixNameProtect(usep) + ".h\"\n");
                    }
                    if (usep->useType().isFwdClass()) {
                        puts("class " + prefixNameProtect(usep) + ";\n");
                    }
                    nl = "\n";
                }
            }
        }
        puts(nl);
    }

    void emitVarReset(AstVar* varp) {
        AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
        const string varNameProtected
            = VN_IS(m_modp, Class) ? varp->nameProtect() : "self->" + varp->nameProtect();
        if (varp->isIO() && m_modp->isTop() && optSystemC()) {
            // System C top I/O doesn't need loading, as the lower level subinst code does it.}
        } else if (varp->isParam()) {
            UASSERT_OBJ(varp->valuep(), varp, "No init for a param?");
            // If a simple CONST value we initialize it using an enum
            // If an ARRAYINIT we initialize it using an initial block similar to a signal
            // puts("// parameter "+varp->nameProtect()+" = "+varp->valuep()->name()+"\n");
        } else if (AstInitArray* initarp = VN_CAST(varp->valuep(), InitArray)) {
            if (AstUnpackArrayDType* adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
                if (initarp->defaultp()) {
                    puts("for (int __Vi=0; __Vi<" + cvtToStr(adtypep->elementsConst()));
                    puts("; ++__Vi) {\n");
                    emitSetVarConstant(varNameProtected + "[__Vi]",
                                       VN_CAST(initarp->defaultp(), Const));
                    puts("}\n");
                }
                const AstInitArray::KeyItemMap& mapr = initarp->map();
                for (const auto& itr : mapr) {
                    AstNode* valuep = itr.second->valuep();
                    emitSetVarConstant(varNameProtected + "[" + cvtToStr(itr.first) + "]",
                                       VN_CAST(valuep, Const));
                }
            } else {
                varp->v3fatalSrc("InitArray under non-arrayed var");
            }
        } else {
            puts(emitVarResetRecurse(varp, varNameProtected, dtypep, 0, ""));
        }
    }
    string emitVarResetRecurse(const AstVar* varp, const string& varNameProtected,
                               AstNodeDType* dtypep, int depth, const string& suffix) {
        dtypep = dtypep->skipRefp();
        AstBasicDType* basicp = dtypep->basicp();
        // Returns string to do resetting, empty to do nothing (which caller should handle)
        if (AstAssocArrayDType* adtypep = VN_CAST(dtypep, AssocArrayDType)) {
            // Access std::array as C array
            string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
            return emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(), depth + 1,
                                       suffix + ".atDefault()" + cvtarray);
        } else if (VN_IS(dtypep, ClassRefDType)) {
            return "";  // Constructor does it
        } else if (AstDynArrayDType* adtypep = VN_CAST(dtypep, DynArrayDType)) {
            // Access std::array as C array
            string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
            return emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(), depth + 1,
                                       suffix + ".atDefault()" + cvtarray);
        } else if (AstQueueDType* adtypep = VN_CAST(dtypep, QueueDType)) {
            // Access std::array as C array
            string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
            return emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(), depth + 1,
                                       suffix + ".atDefault()" + cvtarray);
        } else if (AstUnpackArrayDType* adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            UASSERT_OBJ(adtypep->hi() >= adtypep->lo(), varp,
                        "Should have swapped msb & lsb earlier.");
            string ivar = string("__Vi") + cvtToStr(depth);
            string pre = ("for (int " + ivar + "=" + cvtToStr(0) + "; " + ivar + "<"
                          + cvtToStr(adtypep->elementsConst()) + "; ++" + ivar + ") {\n");
            string below = emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(),
                                               depth + 1, suffix + "[" + ivar + "]");
            string post = "}\n";
            return below.empty() ? "" : pre + below + post;
        } else if (basicp && basicp->keyword() == AstBasicDTypeKwd::STRING) {
            // String's constructor deals with it
            return "";
        } else if (basicp) {
            bool zeroit
                = (varp->attrFileDescr()  // Zero so we don't core dump if never $fopen
                   || (basicp && basicp->isZeroInit())
                   || (v3Global.opt.underlineZero() && !varp->name().empty()
                       && varp->name()[0] == '_')
                   || (v3Global.opt.xInitial() == "fast" || v3Global.opt.xInitial() == "0"));
            splitSizeInc(1);
            if (dtypep->isWide()) {  // Handle unpacked; not basicp->isWide
                string out;
                if (varp->valuep()) {
                    AstConst* const constp = VN_CAST(varp->valuep(), Const);
                    if (!constp) varp->v3fatalSrc("non-const initializer for variable");
                    for (int w = 0; w < varp->widthWords(); ++w) {
                        out += varNameProtected + suffix + "[" + cvtToStr(w) + "] = ";
                        out += cvtToStr(constp->num().edataWord(w)) + "U;\n";
                    }
                } else {
                    out += zeroit ? "VL_ZERO_RESET_W(" : "VL_RAND_RESET_W(";
                    out += cvtToStr(dtypep->widthMin());
                    out += ", " + varNameProtected + suffix + ");\n";
                }
                return out;
            } else {
                string out = varNameProtected + suffix;
                // If --x-initial-edge is set, we want to force an initial
                // edge on uninitialized clocks (from 'X' to whatever the
                // first value is). Since the class is instantiated before
                // initial blocks are evaluated, this should not clash
                // with any initial block settings.
                if (zeroit || (v3Global.opt.xInitialEdge() && varp->isUsedClock())) {
                    out += " = 0;\n";
                } else {
                    out += " = VL_RAND_RESET_";
                    out += dtypep->charIQWN();
                    out += "(" + cvtToStr(dtypep->widthMin()) + ");\n";
                }
                return out;
            }
        } else {
            v3fatalSrc("Unknown node type in reset generator: " << varp->prettyTypeName());
        }
        return "";
    }

    void emitCellCtors(AstNodeModule* modp);
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
    void emitSettleLoop(const std::string& eval_call, bool initial);
    void emitWrapEval(AstNodeModule* modp);
    void emitWrapFast(AstNodeModule* modp);
    void emitMTaskState();
    void emitMTaskVertexCtors(bool* firstp);
    void emitIntTop(AstNodeModule* modp);
    void emitInt(AstNodeModule* modp);
    void maybeSplit();

public:
    EmitCImp() = default;
    virtual ~EmitCImp() override = default;
    void mainImp(AstNodeModule* modp, bool slow);
    void mainInt(AstNodeModule* modp);
    void mainDoFunc(AstCFunc* nodep) { iterate(nodep); }
};

//######################################################################
// Internal EmitCStmts

void EmitCStmts::emitVarDecl(const AstVar* nodep, const string& prefixIfImp) {
    AstBasicDType* basicp = nodep->basicp();
    if (nodep->isIO() && nodep->isSc()) {
        UASSERT_OBJ(basicp, nodep, "Unimplemented: Outputting this data type");
        m_ctorVarsVec.push_back(nodep);
        if (nodep->attrScClocked() && nodep->isReadOnly()) {
            puts("sc_in_clk ");
        } else {
            if (nodep->isInoutish()) {
                puts("sc_inout<");
            } else if (nodep->isWritable()) {
                puts("sc_out<");
            } else if (nodep->isNonOutput()) {
                puts("sc_in<");
            } else {
                nodep->v3fatalSrc("Unknown type");
            }
            puts(nodep->scType());
            puts("> ");
        }
        puts(nodep->nameProtect());
        emitDeclArrayBrackets(nodep);
        puts(";\n");
    } else if (nodep->isIO() && basicp && !basicp->isOpaque()) {
        if (nodep->isInoutish()) {
            puts("VL_INOUT");
        } else if (nodep->isWritable()) {
            puts("VL_OUT");
        } else if (nodep->isNonOutput()) {
            puts("VL_IN");
        } else {
            nodep->v3fatalSrc("Unknown type");
        }

        if (nodep->isQuad()) {
            puts("64");
        } else if (nodep->widthMin() <= 8) {
            puts("8");
        } else if (nodep->widthMin() <= 16) {
            puts("16");
        } else if (nodep->isWide()) {
            puts("W");
        }

        puts("(" + nodep->nameProtect());
        emitDeclArrayBrackets(nodep);
        // If it's a packed struct/array then nodep->width is the whole
        // thing, msb/lsb is just lowest dimension
        puts("," + cvtToStr(basicp->lo() + nodep->width() - 1) + "," + cvtToStr(basicp->lo()));
        if (nodep->isWide()) puts("," + cvtToStr(nodep->widthWords()));
        puts(");\n");
    } else {
        // strings and other fundamental c types
        if (nodep->isFuncLocal() && nodep->isString()) {
            const string name = nodep->name();
            const string suffix = V3Task::dpiTemporaryVarSuffix();
            // string temporary variable for DPI-C needs to be static because c_str() will be
            // passed to C code and the lifetime of the variable must be long enough. See also
            // Issue 2622.
            const bool beStatic = name.size() >= suffix.size()
                                  && name.substr(name.size() - suffix.size()) == suffix;
            if (beStatic) puts("static VL_THREAD_LOCAL ");
        }
        puts(nodep->vlArgType(true, false, false, prefixIfImp));
        puts(";\n");
    }
}

void EmitCStmts::emitCtorSep(bool* firstp) {
    if (*firstp) {
        puts("  : ");
        *firstp = false;
    } else {
        puts(", ");
    }
    if (ofp()->exceededWidth()) puts("\n  ");
}

void EmitCStmts::emitVarCtors(bool* firstp) {
    if (!m_ctorVarsVec.empty()) {
        ofp()->indentInc();
        puts("\n");
        for (const AstVar* varp : m_ctorVarsVec) {
            bool isArray = !VN_CAST(varp->dtypeSkipRefp(), BasicDType);
            if (isArray) {
                puts("// Skipping array: ");
                puts(varp->nameProtect());
                puts("\n");
            } else {
                emitCtorSep(firstp);
                puts(varp->nameProtect());
                puts("(");
                putsQuoted(varp->nameProtect());
                puts(")");
            }
        }
        puts("\n");
        ofp()->indentDec();
    }
}

bool EmitCStmts::emitSimpleOk(AstNodeMath* nodep) {
    // Can we put out a simple (A + B) instead of VL_ADD_III(A,B)?
    if (nodep->emitSimpleOperator() == "") return false;
    if (nodep->isWide()) return false;
    if (nodep->op1p()) {
        if (nodep->op1p()->isWide()) return false;
    }
    if (nodep->op2p()) {
        if (nodep->op2p()->isWide()) return false;
    }
    if (nodep->op3p()) {
        if (nodep->op3p()->isWide()) return false;
    }
    return true;
}

void EmitCStmts::emitOpName(AstNode* nodep, const string& format, AstNode* lhsp, AstNode* rhsp,
                            AstNode* thsp) {
    // Look at emitOperator() format for term/uni/dual/triops,
    // and write out appropriate text.
    //  %n*     node
    //   %nq      emitIQW on the [node]
    //   %nw      width in bits
    //   %nW      width in words
    //   %ni      iterate
    //  %l*     lhsp - if appropriate, then second char as above
    //  %r*     rhsp - if appropriate, then second char as above
    //  %t*     thsp - if appropriate, then second char as above
    //  %k      Potential line break
    //  %P      Wide temporary name
    //  ,       Commas suppressed if the previous field is suppressed
    string nextComma;
    bool needComma = false;
#define COMMA \
    do { \
        if (!nextComma.empty()) { \
            puts(nextComma); \
            nextComma = ""; \
        } \
    } while (false)

    putbs("");
    for (string::const_iterator pos = format.begin(); pos != format.end(); ++pos) {
        if (pos[0] == ',') {
            // Remember we need to add one, but don't do yet to avoid ",)"
            if (needComma) {
                if (pos[1] == ' ') {
                    nextComma = ", ";
                } else
                    nextComma = ",";
                needComma = false;
            }
            if (pos[1] == ' ') ++pos;  // Must do even if no nextComma
        } else if (pos[0] == '%') {
            ++pos;
            bool detail = false;
            AstNode* detailp = nullptr;
            switch (pos[0]) {
            case '%': puts("%"); break;
            case 'k': putbs(""); break;
            case 'n':
                detail = true;
                detailp = nodep;
                break;
            case 'l':
                detail = true;
                detailp = lhsp;
                break;
            case 'r':
                detail = true;
                detailp = rhsp;
                break;
            case 't':
                detail = true;
                detailp = thsp;
                break;
            case 'P':
                if (nodep->isWide()) {
                    UASSERT_OBJ(m_wideTempRefp, nodep,
                                "Wide Op w/ no temp, perhaps missing op in V3EmitC?");
                    COMMA;
                    puts(m_wideTempRefp->hiernameProtect());
                    puts(m_wideTempRefp->varp()->nameProtect());
                    m_wideTempRefp = nullptr;
                    needComma = true;
                }
                break;
            default: nodep->v3fatalSrc("Unknown emitOperator format code: %" << pos[0]); break;
            }
            if (detail) {
                // Get next letter of %[nlrt]
                ++pos;
                switch (pos[0]) {
                case 'q': emitIQW(detailp); break;
                case 'w':
                    COMMA;
                    puts(cvtToStr(detailp->widthMin()));
                    needComma = true;
                    break;
                case 'W':
                    if (lhsp->isWide()) {
                        COMMA;
                        puts(cvtToStr(lhsp->widthWords()));
                        needComma = true;
                    }
                    break;
                case 'i':
                    COMMA;
                    UASSERT_OBJ(detailp, nodep, "emitOperator() references undef node");
                    iterateAndNextNull(detailp);
                    needComma = true;
                    break;
                default:
                    nodep->v3fatalSrc("Unknown emitOperator format code: %[nlrt]" << pos[0]);
                    break;
                }
            }
        } else if (pos[0] == ')') {
            nextComma = "";
            puts(")");
        } else if (pos[0] == '(') {
            COMMA;
            needComma = false;
            puts("(");
        } else {
            // Normal text
            if (isalnum(pos[0])) needComma = true;
            COMMA;
            string s;
            s += pos[0];
            puts(s);
        }
    }
}

//----------------------------------------------------------------------
// Mid level - VISITS

// We only do one display at once, so can just use static state

struct EmitDispState {
    string m_format;  // "%s" and text from user
    std::vector<char> m_argsChar;  // Format of each argument to be printed
    std::vector<AstNode*> m_argsp;  // Each argument to be printed
    std::vector<string> m_argsFunc;  // Function before each argument to be printed
    EmitDispState() { clear(); }
    void clear() {
        m_format = "";
        m_argsChar.clear();
        m_argsp.clear();
        m_argsFunc.clear();
    }
    void pushFormat(const string& fmt) { m_format += fmt; }
    void pushFormat(char fmt) { m_format += fmt; }
    void pushArg(char fmtChar, AstNode* nodep, const string& func) {
        m_argsChar.push_back(fmtChar);
        m_argsp.push_back(nodep);
        m_argsFunc.push_back(func);
    }
} emitDispState;

void EmitCStmts::displayEmit(AstNode* nodep, bool isScan) {
    if (emitDispState.m_format == ""
        && VN_IS(nodep, Display)) {  // not fscanf etc, as they need to return value
        // NOP
    } else {
        // Format
        bool isStmt = false;
        if (const AstFScanF* dispp = VN_CAST(nodep, FScanF)) {
            isStmt = false;
            puts("VL_FSCANF_IX(");
            iterate(dispp->filep());
            puts(",");
        } else if (const AstSScanF* dispp = VN_CAST(nodep, SScanF)) {
            isStmt = false;
            checkMaxWords(dispp->fromp());
            puts("VL_SSCANF_I");
            emitIQW(dispp->fromp());
            puts("X(");
            puts(cvtToStr(dispp->fromp()->widthMin()));
            puts(",");
            iterate(dispp->fromp());
            puts(",");
        } else if (const AstDisplay* dispp = VN_CAST(nodep, Display)) {
            isStmt = true;
            if (dispp->filep()) {
                puts("VL_FWRITEF(");
                iterate(dispp->filep());
                puts(",");
            } else {
                puts("VL_WRITEF(");
            }
        } else if (const AstSFormat* dispp = VN_CAST(nodep, SFormat)) {
            isStmt = true;
            puts("VL_SFORMAT_X(");
            puts(cvtToStr(dispp->lhsp()->widthMin()));
            putbs(",");
            iterate(dispp->lhsp());
            putbs(",");
        } else if (VN_IS(nodep, SFormatF)) {
            isStmt = false;
            puts("VL_SFORMATF_NX(");
        } else {
            nodep->v3fatalSrc("Unknown displayEmit node type");
        }
        ofp()->putsQuoted(emitDispState.m_format);
        // Arguments
        for (unsigned i = 0; i < emitDispState.m_argsp.size(); i++) {
            char fmt = emitDispState.m_argsChar[i];
            AstNode* argp = emitDispState.m_argsp[i];
            string func = emitDispState.m_argsFunc[i];
            if (func != "" || argp) {
                puts(",");
                ofp()->indentInc();
                ofp()->putbs("");
                if (func != "") {
                    puts(func);
                } else if (argp) {
                    bool addrof = isScan || (fmt == '@');
                    if (addrof) puts("&(");
                    iterate(argp);
                    if (!addrof) emitDatap(argp);
                    if (addrof) puts(")");
                }
                ofp()->indentDec();
            }
        }
        // End
        puts(")");
        if (isStmt) {
            puts(";\n");
        } else {
            puts(" ");
        }
        // Prep for next
        emitDispState.clear();
    }
}

void EmitCStmts::displayArg(AstNode* dispp, AstNode** elistp, bool isScan, const string& vfmt,
                            bool ignore, char fmtLetter) {
    // Print display argument, edits elistp
    AstNode* argp = nullptr;
    if (!ignore) {
        argp = *elistp;
        // Prep for next parameter
        *elistp = (*elistp)->nextp();
        if (VL_UNCOVERABLE(!argp)) {
            // expectDisplay() checks this first, so internal error if found here
            dispp->v3error(
                "Internal: Missing arguments for $display-like format");  // LCOV_EXCL_LINE
            return;  // LCOV_EXCL_LINE
        }
        if (argp->widthMin() > VL_VALUE_STRING_MAX_WIDTH) {
            dispp->v3error("Exceeded limit of " + cvtToStr(VL_VALUE_STRING_MAX_WIDTH)
                           + " bits for any $display-like arguments");
        }
        if (argp->widthMin() > 8 && fmtLetter == 'c') {
            // Technically legal, but surely not what the user intended.
            argp->v3warn(WIDTH, dispp->verilogKwd() << "of %c format of > 8 bit value");
        }
    }
    // string pfmt = "%"+displayFormat(argp, vfmt, fmtLetter)+fmtLetter;
    string pfmt;
    if ((fmtLetter == '#' || fmtLetter == 'd') && !isScan
        && vfmt == "") {  // Size decimal output.  Spec says leading spaces, not zeros
        const double mantissabits = ignore ? 0 : (argp->widthMin() - ((fmtLetter == 'd') ? 1 : 0));
        // This is log10(2**mantissabits) as log2(2**mantissabits)/log2(10),
        // + 1.0 rounding bias.
        double dchars = mantissabits / 3.321928094887362 + 1.0;
        if (fmtLetter == 'd') dchars++;  // space for sign
        int nchars = int(dchars);
        pfmt = string("%") + cvtToStr(nchars) + fmtLetter;
    } else {
        pfmt = string("%") + vfmt + fmtLetter;
    }
    emitDispState.pushFormat(pfmt);
    if (!ignore) {
        if (argp->dtypep()->basicp()->keyword() == AstBasicDTypeKwd::STRING) {
            // string in SystemVerilog is std::string in C++ which is not POD
            emitDispState.pushArg(' ', nullptr, "-1");
        } else {
            emitDispState.pushArg(' ', nullptr, cvtToStr(argp->widthMin()));
        }
        emitDispState.pushArg(fmtLetter, argp, "");
        if (fmtLetter == 't' || fmtLetter == '^') {
            AstSFormatF* fmtp = nullptr;
            if (AstDisplay* nodep = VN_CAST(dispp, Display))
                fmtp = nodep->fmtp();
            else if (AstSFormat* nodep = VN_CAST(dispp, SFormat))
                fmtp = nodep->fmtp();
            else
                fmtp = VN_CAST(dispp, SFormatF);
            UASSERT_OBJ(fmtp, dispp,
                        "Use of %t must be under AstDisplay, AstSFormat, or AstSFormatF");
            UASSERT_OBJ(!fmtp->timeunit().isNone(), fmtp, "timenunit must be set");
            emitDispState.pushArg(' ', nullptr, cvtToStr((int)fmtp->timeunit().powerOfTen()));
        }
    } else {
        emitDispState.pushArg(fmtLetter, nullptr, "");
    }
}

void EmitCStmts::displayNode(AstNode* nodep, AstScopeName* scopenamep, const string& vformat,
                             AstNode* exprsp, bool isScan) {
    AstNode* elistp = exprsp;

    // Convert Verilog display to C printf formats
    //          "%0t" becomes "%d"
    emitDispState.clear();
    string vfmt;
    string::const_iterator pos = vformat.begin();
    bool inPct = false;
    bool ignore = false;
    for (; pos != vformat.end(); ++pos) {
        // UINFO(1, "Parse '" << *pos << "'  IP" << inPct << " List " << cvtToHex(elistp) << endl);
        if (!inPct && pos[0] == '%') {
            inPct = true;
            ignore = false;
            vfmt = "";
        } else if (!inPct) {  // Normal text
            emitDispState.pushFormat(*pos);
        } else {  // Format character
            inPct = false;
            switch (tolower(pos[0])) {
            case '0':  // FALLTHRU
            case '1':  // FALLTHRU
            case '2':  // FALLTHRU
            case '3':  // FALLTHRU
            case '4':  // FALLTHRU
            case '5':  // FALLTHRU
            case '6':  // FALLTHRU
            case '7':  // FALLTHRU
            case '8':  // FALLTHRU
            case '9':  // FALLTHRU
            case '.':  // FALLTHRU
            case '-':
                // Digits, like %5d, etc.
                vfmt += pos[0];
                inPct = true;  // Get more digits
                break;
            case '%':
                emitDispState.pushFormat("%%");  // We're printf'ing it, so need to quote the %
                break;
            case '*':
                vfmt += pos[0];
                inPct = true;  // Get more digits
                ignore = true;
                break;
            // Special codes
            case '~':
                displayArg(nodep, &elistp, isScan, vfmt, ignore, 'd');
                break;  // Signed decimal
            case '@':
                displayArg(nodep, &elistp, isScan, vfmt, ignore, '@');
                break;  // Packed string
            // Spec: h d o b c l
            case 'b': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'b'); break;
            case 'c': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'c'); break;
            case 't': displayArg(nodep, &elistp, isScan, vfmt, ignore, 't'); break;
            case 'd':
                displayArg(nodep, &elistp, isScan, vfmt, ignore, '#');
                break;  // Unsigned decimal
            case 'o': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'o'); break;
            case 'h':  // FALLTHRU
            case 'x': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'x'); break;
            case 's': displayArg(nodep, &elistp, isScan, vfmt, ignore, 's'); break;
            case 'e': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'e'); break;
            case 'f': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'f'); break;
            case 'g': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'g'); break;
            case '^': displayArg(nodep, &elistp, isScan, vfmt, ignore, '^'); break;  // Realtime
            case 'v': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'v'); break;
            case 'u': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'u'); break;
            case 'z': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'z'); break;
            case 'm': {
                UASSERT_OBJ(scopenamep, nodep, "Display with %m but no AstScopeName");
                string suffix = scopenamep->scopePrettySymName();
                if (suffix == "") {
                    emitDispState.pushFormat("%S");
                } else {
                    emitDispState.pushFormat("%N");  // Add a . when needed
                }
                emitDispState.pushArg(' ', nullptr, "vlSymsp->name()");
                emitDispState.pushFormat(suffix);
                break;
            }
            case 'l': {
                // Better than not compiling
                emitDispState.pushFormat("----");
                break;
            }
            default:
                nodep->v3error("Unknown $display-like format code: '%" << pos[0] << "'");
                break;
            }
        }
    }
    if (VL_UNCOVERABLE(elistp)) {
        // expectFormat also checks this, and should have found it first, so internal
        elistp->v3error("Internal: Extra arguments for $display-like format");  // LCOV_EXCL_LINE
    }
    displayEmit(nodep, isScan);
}

//######################################################################
// Internal EmitC

void EmitCImp::emitCoverageDecl(AstNodeModule*) {
    if (v3Global.opt.coverage()) {
        ofp()->putsPrivate(true);
        putsDecoration("// Coverage\n");
        puts("void __vlCoverInsert(");
        puts(v3Global.opt.threads() ? "std::atomic<uint32_t>" : "uint32_t");
        puts("* countp, bool enable, const char* filenamep, int lineno, int column,\n");
        puts("const char* hierp, const char* pagep, const char* commentp, const char* "
             "linescovp);\n");
    }
}

void EmitCImp::emitMTaskVertexCtors(bool* firstp) {
    AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
    UASSERT_OBJ(execGraphp, v3Global.rootp(), "Root should have an execGraphp");
    const V3Graph* depGraphp = execGraphp->depGraphp();

    unsigned finalEdgesInCt = 0;
    for (const V3GraphVertex* vxp = depGraphp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        const ExecMTask* mtp = dynamic_cast<const ExecMTask*>(vxp);
        unsigned edgesInCt = packedMTaskMayBlock(mtp);
        if (packedMTaskMayBlock(mtp) > 0) {
            emitCtorSep(firstp);
            puts("__Vm_mt_" + cvtToStr(mtp->id()) + "(" + cvtToStr(edgesInCt) + ")");
        }
        // Each mtask with no packed successor will become a dependency
        // for the final node:
        if (!mtp->packNextp()) ++finalEdgesInCt;
    }

    emitCtorSep(firstp);
    puts("__Vm_mt_final(" + cvtToStr(finalEdgesInCt) + ")");

    // This will flip to 'true' before the start of the 0th cycle.
    emitCtorSep(firstp);
    puts("__Vm_threadPoolp(nullptr)");
    if (v3Global.opt.profThreads()) {
        emitCtorSep(firstp);
        puts("__Vm_profile_cycle_start(0)");
    }
    emitCtorSep(firstp);
    puts("__Vm_even_cycle(false)");
}

void EmitCImp::emitCtorImp(AstNodeModule* modp) {
    puts("\n");
    bool first = true;
    string section;
    emitParams(modp, true, &first, section /*ref*/);

    if (VN_IS(modp, Class)) {
        modp->v3fatalSrc("constructors should be AstCFuncs instead");
    } else if (optSystemC() && modp->isTop()) {
        puts(prefixNameProtect(modp) + "::" + prefixNameProtect(modp) + "(sc_module_name)");
    } else if (modp->isTop()) {
        puts(prefixNameProtect(modp) + "::" + prefixNameProtect(modp)
             + "(VerilatedContext* _vcontextp__, const char* _vcname__)\n");
        puts("    : VerilatedModule{_vcname__}\n");
        first = false;  // printed the first ':'
    } else {
        puts(prefixNameProtect(modp) + "::" + prefixNameProtect(modp)
             + "(const char* _vcname__)\n");
        puts("    : VerilatedModule(_vcname__)\n");
    }
    emitVarCtors(&first);
    if (modp->isTop() && v3Global.opt.mtasks()) emitMTaskVertexCtors(&first);

    puts(" {\n");
    emitCellCtors(modp);
    emitSensitives();

    putsDecoration("// Reset internal values\n");
    if (modp->isTop()) {
        if (v3Global.opt.inhibitSim()) puts("__Vm_inhibitSim = false;\n");
        puts("\n");
    }
    putsDecoration("// Reset structure values\n");
    puts(protect("_ctor_var_reset") + "(this);\n");
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

        if (v3Global.opt.profThreads()) {
            puts("__Vm_profile_cycle_start = 0;\n");
            puts("__Vm_profile_time_finished = 0;\n");
            puts("__Vm_profile_window_ct = 0;");
        }
    }
    puts("}\n");
}

void EmitCImp::emitConfigureImp(AstNodeModule* modp) {
    puts("\nvoid " + prefixNameProtect(modp) + "::" + protect("__Vconfigure") + "("
         + symClassName() + "* vlSymsp, bool first) {\n");
    puts("if (false && first) {}  // Prevent unused\n");
    puts("this->__VlSymsp = vlSymsp;\n");  // First, as later stuff needs it.
    puts("if (false && this->__VlSymsp) {}  // Prevent unused\n");
    if (v3Global.opt.coverage()) {
        puts(protect("_configure_coverage") + "(this, vlSymsp, first);\n");
    }
    if (modp->isTop() && !v3Global.rootp()->timeunit().isNone()) {
        puts("vlSymsp->_vm_contextp__->timeunit("
             + cvtToStr(v3Global.rootp()->timeunit().powerOfTen()) + ");\n");
    }
    if (modp->isTop() && !v3Global.rootp()->timeprecision().isNone()) {
        puts("vlSymsp->_vm_contextp__->timeprecision("
             + cvtToStr(v3Global.rootp()->timeprecision().powerOfTen()) + ");\n");
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
        puts("VL_COVER_INSERT(__VlSymsp->_vm_contextp__->coveragep(), count32p,");
        puts("  \"filename\",filenamep,");
        puts("  \"lineno\",lineno,");
        puts("  \"column\",column,\n");
        // Need to move hier into scopes and back out if do this
        // puts( "\"hier\",std::string(__VlSymsp->name())+hierp,");
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
            puts("if (VL_UNLIKELY(__VlSymsp->__Vm_dumping)) _traceDumpClose();\n");
            puts("#endif  // VM_TRACE\n");
        }
    }
    emitTextSection(AstType::atScDtor);
    if (modp->isTop()) puts("VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = nullptr);\n");
    puts("}\n");
    splitSizeInc(10);
}

void EmitCImp::emitSavableImp(AstNodeModule* modp) {
    if (v3Global.opt.savable()) {
        puts("\n// Savable\n");
        for (int de = 0; de < 2; ++de) {
            string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
            string funcname = de ? "__Vdeserialize" : "__Vserialize";
            string op = de ? ">>" : "<<";
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
            puts("os " + op + " __VlSymsp->_vm_contextp__;\n");

            // Save all members
            if (v3Global.opt.inhibitSim()) puts("os" + op + "__Vm_inhibitSim;\n");
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
                            int vecnum = vects++;
                            UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                        "Should have swapped msb & lsb earlier.");
                            string ivar = string("__Vi") + cvtToStr(vecnum);
                            puts("for (int __Vi" + cvtToStr(vecnum) + "=" + cvtToStr(0));
                            puts("; " + ivar + "<" + cvtToStr(arrayp->elementsConst()));
                            puts("; ++" + ivar + ") {\n");
                            elementp = arrayp->subDTypep()->skipRefp();
                        }
                        // Want to detect types that are represented as arrays
                        // (i.e. packed types of more than 64 bits).
                        AstBasicDType* basicp = elementp->basicp();
                        if (elementp->isWide()
                            && !(basicp && basicp->keyword() == AstBasicDTypeKwd::STRING)) {
                            int vecnum = vects++;
                            string ivar = string("__Vi") + cvtToStr(vecnum);
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
                puts("__VlSymsp->" + protect(funcname) + "(os);\n");
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

void EmitCImp::emitCellCtors(AstNodeModule* modp) {
    if (modp->isTop()) {
        // Must be before other constructors, as __vlCoverInsert calls it
        // Note _vcontextp__ may be nullptr, VerilatedSyms::VerilatedSyms cleans it up
        puts(EmitCBaseVisitor::symClassVar() + " = __VlSymsp = new " + symClassName() + "("
             + (optSystemC() ? "nullptr" : "_vcontextp__") + ", this, name());\n");
        puts(EmitCBaseVisitor::symTopAssign() + "\n");
    }
    for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (AstCell* cellp = VN_CAST(nodep, Cell)) {
            puts("VL_CELL(" + cellp->nameProtect() + ", " + prefixNameProtect(cellp->modp())
                 + ");\n");
        }
    }
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
                        int vecnum = vects++;
                        UASSERT_OBJ(arrayp->hi() >= arrayp->lo(), varp,
                                    "Should have swapped msb & lsb earlier.");
                        string ivar = string("__Vi") + cvtToStr(vecnum);
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

void EmitCImp::emitSettleLoop(const std::string& eval_call, bool initial) {
    putsDecoration("// Evaluate till stable\n");
    puts("int __VclockLoop = 0;\n");
    puts("QData __Vchange = 1;\n");
    puts("do {\n");
    puts(eval_call + "\n");
    puts("if (VL_UNLIKELY(++__VclockLoop > " + cvtToStr(v3Global.opt.convergeLimit()) + ")) {\n");
    puts("// About to fail, so enable debug to see what's not settling.\n");
    puts("// Note you must run make with OPT=-DVL_DEBUG for debug prints.\n");
    puts("int __Vsaved_debug = Verilated::debug();\n");
    puts("Verilated::debug(1);\n");
    puts("__Vchange = " + protect("_change_request") + "(vlSymsp);\n");
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
    puts("__Vchange = " + protect("_change_request") + "(vlSymsp);\n");
    puts("}\n");
    puts("} while (VL_UNLIKELY(__Vchange));\n");
}

void EmitCImp::emitWrapFast(AstNodeModule* modp) {
    puts("\nVerilatedContext* " + prefixNameProtect(modp) + "::contextp() {\n");
    puts(/**/ "return __VlSymsp->_vm_contextp__;\n");
    puts("}\n");
}

void EmitCImp::emitWrapEval(AstNodeModule* modp) {
    puts("\nvoid " + prefixNameProtect(modp) + "::eval_step() {\n");
    puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+++++TOP Evaluate " + prefixNameProtect(modp)
         + "::eval\\n\"); );\n");
    puts(EmitCBaseVisitor::symClassVar() + " = this->__VlSymsp;  // Setup global symbol table\n");
    puts(EmitCBaseVisitor::symTopAssign() + "\n");
    puts("#ifdef VL_DEBUG\n");
    putsDecoration("// Debug assertions\n");
    puts(protect("_eval_debug_assertions") + "();\n");
    puts("#endif  // VL_DEBUG\n");
    putsDecoration("// Initialize\n");
    puts("if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) " + protect("_eval_initial_loop")
         + "(vlSymsp);\n");
    if (v3Global.opt.inhibitSim()) puts("if (VL_UNLIKELY(__Vm_inhibitSim)) return;\n");

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
        puts("if (vlTOPp->__Vm_profile_window_ct == 0) {\n");  // Opening file?
        // Start profile on this cycle. We'll capture a window worth, then
        // only analyze the next window worth. The idea is that the first window
        // capture will hit some cache-cold stuff (eg printf) but it'll be warm
        // by the time we hit the second window, we hope.
        puts("vlTOPp->__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
        // "* 2" as first half is warmup, second half is collection
        puts("vlTOPp->__Vm_profile_window_ct = vlSymsp->_vm_contextp__->profThreadsWindow() * 2 + "
             "1;\n");
        puts("}\n");
        puts("--vlTOPp->__Vm_profile_window_ct;\n");
        puts("if (vlTOPp->__Vm_profile_window_ct == "
             "(vlSymsp->_vm_contextp__->profThreadsWindow())) {\n");
        // This barrier record in every threads' profile demarcates the
        // cache-warm-up cycles before the barrier from the actual profile
        // cycles afterward.
        puts("vlTOPp->__Vm_threadPoolp->profileAppendAll(");
        puts("VlProfileRec(VlProfileRec::Barrier()));\n");
        puts("vlTOPp->__Vm_profile_cycle_start = VL_RDTSC_Q();\n");
        puts("}\n");
        puts("else if (vlTOPp->__Vm_profile_window_ct == 0) {\n");
        // Ending file.
        puts("vluint64_t elapsed = VL_RDTSC_Q() - vlTOPp->__Vm_profile_cycle_start;\n");
        puts(
            "vlTOPp->__Vm_threadPoolp->profileDump(vlSymsp->_vm_contextp__->profThreadsFilename()."
            "c_str(), elapsed);\n");
        // This turns off the test to enter the profiling code, but still
        // allows the user to collect another profile by changing
        // profThreadsStart
        puts("__Vm_profile_time_finished = vlSymsp->_vm_contextp__->profThreadsStart();\n");
        puts("vlTOPp->__Vm_profile_cycle_start = 0;\n");
        puts("}\n");
        puts("}\n");
    }

    emitSettleLoop((string("VL_DEBUG_IF(VL_DBG_MSGF(\"+ Clock loop\\n\"););\n")
                    + (v3Global.opt.trace() ? "vlSymsp->__Vm_activity = true;\n" : "")
                    + protect("_eval") + "(vlSymsp);"),
                   false);
    if (v3Global.opt.threads() == 1) {
        puts("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");
    }
    if (v3Global.opt.threads()) puts("Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);\n");
    puts("}\n");
    splitSizeInc(10);

    //
    if (v3Global.needTraceDumper() && !optSystemC()) {
        puts("\nvoid " + prefixNameProtect(modp) + "::eval_end_step() {\n");
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+eval_end_step " + prefixNameProtect(modp)
             + "::eval_end_step\\n\"); );\n");
        puts("#ifdef VM_TRACE\n");
        puts(EmitCBaseVisitor::symClassVar()
             + " = this->__VlSymsp;  // Setup global symbol table\n");
        puts(EmitCBaseVisitor::symTopAssign() + "\n");
        putsDecoration("// Tracing\n");
        // SystemC's eval loop deals with calling trace, not us
        puts("if (VL_UNLIKELY(vlSymsp->__Vm_dumping)) _traceDump();\n");
        puts("#endif  // VM_TRACE\n");
        puts("}\n");
    }

    //
    puts("\nvoid " + prefixNameProtect(modp) + "::" + protect("_eval_initial_loop") + "("
         + EmitCBaseVisitor::symClassVar() + ") {\n");
    puts("vlSymsp->__Vm_didInit = true;\n");
    puts(protect("_eval_initial") + "(vlSymsp);\n");
    if (v3Global.opt.trace()) puts("vlSymsp->__Vm_activity = true;\n");
    emitSettleLoop((protect("_eval_settle") + "(vlSymsp);\n"  //
                    + protect("_eval") + "(vlSymsp);"),
                   true);
    puts("}\n");
    splitSizeInc(10);
}

//----------------------------------------------------------------------
// Top interface/ implementation

void EmitCStmts::emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp,
                             string& sectionr) {
    // Put out a list of signal declarations
    // in order of 0:clocks, 1:vluint8, 2:vluint16, 4:vluint32, 5:vluint64, 6:wide, 7:arrays
    // This aids cache packing and locality
    //
    // Largest->smallest reduces the number of pad variables.  Also
    // experimented with alternating between large->small and small->large
    // on successive Mtask groups, but then when a new mtask gets added may
    // cause a huge delta.
    //
    // TODO: Move this sort to an earlier visitor stage.
    VarSortMap varAnonMap;
    VarSortMap varNonanonMap;

    for (int isstatic = 1; isstatic >= 0; isstatic--) {
        if (prefixIfImp != "" && !isstatic) continue;
        for (AstNode* nodep = firstp; nodep; nodep = nodep->nextp()) {
            if (const AstVar* varp = VN_CAST(nodep, Var)) {
                bool doit = true;
                switch (which) {
                case EVL_CLASS_IO: doit = varp->isIO(); break;
                case EVL_CLASS_SIG:
                    doit = ((varp->isSignal() || varp->isClassMember()) && !varp->isIO());
                    break;
                case EVL_CLASS_TEMP: doit = (varp->isTemp() && !varp->isIO()); break;
                case EVL_CLASS_PAR:
                    doit = (varp->isParam() && !VN_IS(varp->valuep(), Const));
                    break;
                case EVL_CLASS_ALL: doit = true; break;
                case EVL_FUNC_ALL: doit = true; break;
                default: v3fatalSrc("Bad Case");
                }
                if (varp->isStatic() ? !isstatic : isstatic) doit = false;
                if (doit) {
                    int sigbytes = varp->dtypeSkipRefp()->widthAlignBytes();
                    int sortbytes = 9;
                    if (varp->isUsedClock() && varp->widthMin() == 1) {
                        sortbytes = 0;
                    } else if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) {
                        sortbytes = 8;
                    } else if (varp->basicp() && varp->basicp()->isOpaque()) {
                        sortbytes = 7;
                    } else if (varp->isScBv() || varp->isScBigUint()) {
                        sortbytes = 6;
                    } else if (sigbytes == 8) {
                        sortbytes = 5;
                    } else if (sigbytes == 4) {
                        sortbytes = 4;
                    } else if (sigbytes == 2) {
                        sortbytes = 2;
                    } else if (sigbytes == 1) {
                        sortbytes = 1;
                    }
                    bool anonOk = (v3Global.opt.compLimitMembers() != 0  // Enabled
                                   && !varp->isStatic() && !varp->isIO()  // Confusing to user
                                   && !varp->isSc()  // Aggregates can't be anon
                                   && (varp->basicp()
                                       && !varp->basicp()->isOpaque())  // Aggregates can't be anon
                                   && which != EVL_FUNC_ALL);  // Anon not legal in funcs, and gcc
                                                               // bug free there anyhow
                    if (anonOk) {
                        varAnonMap[sortbytes].push_back(varp);
                    } else {
                        varNonanonMap[sortbytes].push_back(varp);
                    }
                }
            }
        }
    }

    if (!varAnonMap.empty() || !varNonanonMap.empty()) {
        if (!sectionr.empty()) {
            puts(sectionr);
            sectionr = "";
        }
        VarVec anons;
        VarVec nonanons;
        emitVarSort(varAnonMap, &anons);
        emitVarSort(varNonanonMap, &nonanons);
        emitSortedVarList(anons, nonanons, prefixIfImp);
    }
}

void EmitCStmts::emitVarSort(const VarSortMap& vmap, VarVec* sortedp) {
    UASSERT(sortedp->empty(), "Sorted should be initially empty");
    if (!v3Global.opt.mtasks()) {
        // Plain old serial mode. Sort by size, from small to large,
        // to optimize for both packing and small offsets in code.
        for (const auto& itr : vmap) {
            for (VarVec::const_iterator jt = itr.second.begin(); jt != itr.second.end(); ++jt) {
                sortedp->push_back(*jt);
            }
        }
        return;
    }

    // MacroTask mode.  Sort by MTask-affinity group first, size second.
    using MTaskVarSortMap = std::map<const MTaskIdSet, VarSortMap>;
    MTaskVarSortMap m2v;
    for (VarSortMap::const_iterator it = vmap.begin(); it != vmap.end(); ++it) {
        int size_class = it->first;
        const VarVec& vec = it->second;
        for (const AstVar* varp : vec) { m2v[varp->mtaskIds()][size_class].push_back(varp); }
    }

    // Create a TSP sort state for each MTaskIdSet footprint
    V3TSP::StateVec states;
    for (MTaskVarSortMap::iterator it = m2v.begin(); it != m2v.end(); ++it) {
        states.push_back(new EmitVarTspSorter(it->first));
    }

    // Do the TSP sort
    V3TSP::StateVec sorted_states;
    V3TSP::tspSort(states, &sorted_states);

    for (V3TSP::StateVec::iterator it = sorted_states.begin(); it != sorted_states.end(); ++it) {
        const EmitVarTspSorter* statep = dynamic_cast<const EmitVarTspSorter*>(*it);
        const VarSortMap& localVmap = m2v[statep->mtaskIds()];
        // use rbegin/rend to sort size large->small
        for (VarSortMap::const_reverse_iterator jt = localVmap.rbegin(); jt != localVmap.rend();
             ++jt) {
            const VarVec& vec = jt->second;
            for (VarVec::const_iterator kt = vec.begin(); kt != vec.end(); ++kt) {
                sortedp->push_back(*kt);
            }
        }
        VL_DO_DANGLING(delete statep, statep);
    }
}

void EmitCStmts::emitSortedVarList(const VarVec& anons, const VarVec& nonanons,
                                   const string& prefixIfImp) {
    string curVarCmt;
    // Output anons
    {
        int anonMembers = anons.size();
        int lim = v3Global.opt.compLimitMembers();
        int anonL3s = 1;
        int anonL2s = 1;
        int anonL1s = 1;
        if (anonMembers > (lim * lim * lim)) {
            anonL3s = (anonMembers + (lim * lim * lim) - 1) / (lim * lim * lim);
            anonL2s = lim;
            anonL1s = lim;
        } else if (anonMembers > (lim * lim)) {
            anonL2s = (anonMembers + (lim * lim) - 1) / (lim * lim);
            anonL1s = lim;
        } else if (anonMembers > lim) {
            anonL1s = (anonMembers + lim - 1) / lim;
        }
        if (anonL1s != 1)
            puts("// Anonymous structures to workaround compiler member-count bugs\n");
        auto it = anons.cbegin();
        for (int l3 = 0; l3 < anonL3s && it != anons.cend(); ++l3) {
            if (anonL3s != 1) puts("struct {\n");
            for (int l2 = 0; l2 < anonL2s && it != anons.cend(); ++l2) {
                if (anonL2s != 1) puts("struct {\n");
                for (int l1 = 0; l1 < anonL1s && it != anons.cend(); ++l1) {
                    if (anonL1s != 1) puts("struct {\n");
                    for (int l0 = 0; l0 < lim && it != anons.cend(); ++l0) {
                        const AstVar* varp = *it;
                        emitVarCmtChg(varp, &curVarCmt);
                        emitVarDecl(varp, prefixIfImp);
                        ++it;
                    }
                    if (anonL1s != 1) puts("};\n");
                }
                if (anonL2s != 1) puts("};\n");
            }
            if (anonL3s != 1) puts("};\n");
        }
        // Leftovers, just in case off by one error somewhere above
        for (; it != anons.end(); ++it) {
            const AstVar* varp = *it;
            emitVarCmtChg(varp, &curVarCmt);
            emitVarDecl(varp, prefixIfImp);
        }
    }
    // Output nonanons
    for (const AstVar* varp : nonanons) {
        emitVarCmtChg(varp, &curVarCmt);
        emitVarDecl(varp, prefixIfImp);
    }
}

void EmitCImp::emitMTaskState() {
    ofp()->putsPrivate(true);
    AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
    UASSERT_OBJ(execGraphp, v3Global.rootp(), "Root should have an execGraphp");

    const V3Graph* depGraphp = execGraphp->depGraphp();
    for (const V3GraphVertex* vxp = depGraphp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        const ExecMTask* mtp = dynamic_cast<const ExecMTask*>(vxp);
        if (packedMTaskMayBlock(mtp) > 0) {
            puts("VlMTaskVertex __Vm_mt_" + cvtToStr(mtp->id()) + ";\n");
        }
    }
    // This fake mtask depends on all the real ones.  We use it to block
    // eval() until all mtasks are done.
    //
    // In the future we might allow _eval() to return before the graph is
    // fully done executing, for "half wave" scheduling. For now we wait
    // for all mtasks though.
    puts("VlMTaskVertex __Vm_mt_final;\n");
    puts("VlThreadPool* __Vm_threadPoolp;\n");

    if (v3Global.opt.profThreads()) {
        // rdtsc() at current cycle start
        puts("vluint64_t __Vm_profile_cycle_start;\n");
        // Time we finished analysis
        puts("vluint64_t __Vm_profile_time_finished;\n");
        // Track our position in the cache warmup and actual profile window
        puts("vluint32_t __Vm_profile_window_ct;\n");
    }

    puts("bool __Vm_even_cycle;\n");
}

void EmitCImp::emitIntTop(AstNodeModule*) {
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
    if (v3Global.dpi()) {
        // do this before including our main .h file so that any references to
        // types defined in svdpi.h are available
        puts("#include \"" + topClassName() + "__Dpi.h\"\n");
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
        ofp()->putsPrivate(!modp->isTop());  // private: unless top
        puts(symClassName() + "* __VlSymsp;  // Symbol table\n");
    }
    ofp()->putsPrivate(false);  // public:
    if (modp->isTop()) {
        if (v3Global.opt.inhibitSim()) {
            puts("bool __Vm_inhibitSim;  ///< Set true to disable evaluation of module\n");
        }
        if (v3Global.opt.mtasks()) emitMTaskState();
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
        puts("VerilatedContext* contextp();\n");

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
        if (v3Global.opt.inhibitSim()) {
            puts("/// Disable evaluation of module (e.g. turn off)\n");
            puts("void inhibitSim(bool flag) { __Vm_inhibitSim = flag; }\n");
        }
    }

    puts("\n// INTERNAL METHODS\n");
    if (modp->isTop()) {
        ofp()->putsPrivate(false);  // public: as accessed by another VL_MODULE
        puts("static void " + protect("_eval_initial_loop") + "(" + EmitCBaseVisitor::symClassVar()
             + ");\n");
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

    if (v3Global.opt.trace() && !VN_IS(modp, Class)) {
        ofp()->putsPrivate(true);  // private:
        puts("static void " + protect("traceInit") + "(void* userp, "
             + v3Global.opt.traceClassBase() + "* tracep, uint32_t code) VL_ATTR_COLD;\n");
    }
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
            emitWrapFast(modp);
            emitWrapEval(modp);
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

    if (m_fast && modp->isTop() && v3Global.opt.mtasks()) {
        // Make a final pass and emit function definitions for the mtasks
        // in the ExecGraph
        AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
        const V3Graph* depGraphp = execGraphp->depGraphp();
        for (const V3GraphVertex* vxp = depGraphp->verticesBeginp(); vxp;
             vxp = vxp->verticesNextp()) {
            const ExecMTask* mtaskp = dynamic_cast<const ExecMTask*>(vxp);
            if (mtaskp->threadRoot()) {
                // Only define one function for all the mtasks packed on
                // a given thread. We'll name this function after the
                // root mtask though it contains multiple mtasks' worth
                // of logic.
                iterate(mtaskp->bodyp());
            }
        }
    }
    VL_DO_CLEAR(delete m_ofp, m_ofp = nullptr);
}

//######################################################################
// Tracing routines

class EmitCTrace final : EmitCStmts {
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user1()        -> int.  Enum number
    AstUser1InUse m_inuser1;

    // MEMBERS
    AstCFunc* m_cfuncp = nullptr;  // Function we're in now
    bool m_slow;  // Making slow file
    int m_enumNum = 0;  // Enumeration number (whole netlist)
    int m_baseCode = -1;  // Code of first AstTraceInc in this function

    // METHODS
    void newOutCFile(int filenum) {
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
        puts("\n//======================\n\n");

        if (v3Global.needTraceDumper() && !optSystemC()) {
            puts("void " + topClassName() + "::_traceDump() {\n");
            // Caller checked for __Vm_dumperp non-nullptr
            puts("const VerilatedLockGuard lock(__VlSymsp->__Vm_dumperMutex);\n");
            puts("__VlSymsp->__Vm_dumperp->dump(VL_TIME_Q());\n");
            puts("}\n");
            splitSizeInc(10);
        }

        if (v3Global.needTraceDumper()) {
            puts("void " + topClassName() + "::_traceDumpOpen() {\n");
            puts("const VerilatedLockGuard lock(__VlSymsp->__Vm_dumperMutex);\n");
            puts("if (VL_UNLIKELY(!__VlSymsp->__Vm_dumperp)) {\n");
            puts("__VlSymsp->__Vm_dumperp = new " + v3Global.opt.traceClassLang() + "();\n");
            puts("trace(__VlSymsp->__Vm_dumperp, 0, 0);\n");
            puts("std::string dumpfile = __VlSymsp->_vm_contextp__->dumpfileCheck();\n");
            puts("__VlSymsp->__Vm_dumperp->open(dumpfile.c_str());\n");
            puts("__VlSymsp->__Vm_dumping = true;\n");
            puts("}\n");
            puts("}\n");
            splitSizeInc(10);

            puts("void " + topClassName() + "::_traceDumpClose() {\n");
            puts("const VerilatedLockGuard lock(__VlSymsp->__Vm_dumperMutex);\n");
            puts("__VlSymsp->__Vm_dumping = false;\n");
            puts("VL_DO_CLEAR(delete __VlSymsp->__Vm_dumperp, __VlSymsp->__Vm_dumperp = "
                 "nullptr);\n");
            puts("}\n");
            splitSizeInc(10);
        }

        puts("void " + topClassName() + "::trace(");
        puts(v3Global.opt.traceClassBase() + "C* tfp, int, int) {\n");
        puts("tfp->spTrace()->addInitCb(&" + protect("traceInit") + ", __VlSymsp);\n");
        puts(protect("traceRegister") + "(tfp->spTrace());\n");
        puts("}\n");
        puts("\n");
        splitSizeInc(10);

        puts("void " + topClassName() + "::" + protect("traceInit") + "(void* userp, "
             + v3Global.opt.traceClassBase() + "* tracep, uint32_t code) {\n");
        putsDecoration("// Callback from tracep->open()\n");
        puts(symClassVar() + " = static_cast<" + symClassName() + "*>(userp);\n");
        puts("if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {\n");
        puts("VL_FATAL_MT(__FILE__, __LINE__, __FILE__,\n");
        puts("            \"Turning on wave traces requires Verilated::traceEverOn(true) call "
             "before time 0.\");\n");
        puts("}\n");
        puts("vlSymsp->__Vm_baseCode = code;\n");
        puts("tracep->module(vlSymsp->name());\n");
        puts("tracep->scopeEscape(' ');\n");
        puts(topClassName() + "::" + protect("traceInitTop") + "(vlSymsp, tracep);\n");
        puts("tracep->scopeEscape('.');\n");  // Restore so later traced files won't break
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
            AstVarType vartype = nodep->varType();
            AstBasicDTypeKwd kwd = nodep->declKwd();
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
    using EmitCStmts::visit;  // Suppress hidden overloaded virtual function warning
    virtual void visit(AstNetlist* nodep) override {
        // Top module only
        iterate(nodep->topModulep());
    }
    virtual void visit(AstNodeModule* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstCFunc* nodep) override {
        if (nodep->slow() != m_slow) return;
        VL_RESTORER(m_cfuncp);
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
            puts(nodep->rtnTypeVoid());
            puts(" ");
            puts(topClassName() + "::" + nodep->nameProtect() + "(" + cFuncArgs(nodep) + ") {\n");

            if (nodep->funcType() != AstCFuncType::TRACE_REGISTER) {
                puts(symClassVar() + " = static_cast<" + symClassName() + "*>(userp);\n");
            }

            if (nodep->symProlog()) puts(symTopAssign() + "\n");

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

            if (nodep->initsp()) {
                string section;
                putsDecoration("// Variables\n");
                emitVarList(nodep->initsp(), EVL_FUNC_ALL, "", section /*ref*/);
                iterateAndNextNull(nodep->initsp());
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
        int enumNum = emitTraceDeclDType(nodep->dtypep());
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

void V3EmitC::emitc() {
    UINFO(2, __FUNCTION__ << ": " << endl);
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
            EmitCStmts visitor(cfilep->tblockp(), &of, true);
        }
    }
}
