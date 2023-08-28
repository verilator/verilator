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

#ifndef VERILATOR_V3EMITCFUNC_H_
#define VERILATOR_V3EMITCFUNC_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3EmitCConstInit.h"
#include "V3Global.h"
#include "V3MemberMap.h"

#include <algorithm>
#include <map>
#include <unordered_set>
#include <vector>

// Number of VL_CONST_W_*X's in verilated.h (IE VL_CONST_W_8X is last)
constexpr int EMITC_NUM_CONSTW = 8;

//######################################################################
// Emit lazy forward declarations

class EmitCLazyDecls final : public VNVisitorConst {
    // NODE STATE/TYPES
    // None allowed to support threaded emitting

    // MEMBERS
    std::unordered_set<string> m_emittedManually;  // Set of names already declared manually.
    EmitCBaseVisitorConst& m_emitter;  // For access to file output
    bool m_needsBlankLine = false;  // Emit blank line if any declarations were emitted (cosmetic)
    std::set<AstNode*> m_emitted;  // -> in set. Already emitted decl for symbols.

    // METHODS
    bool declaredOnce(AstNode* nodep) { return m_emitted.insert(nodep).second; }

    void lazyDeclare(AstCFunc* funcp) {
        // Already declared in this compilation unit
        if (!declaredOnce(funcp)) return;
        // Check if this kind of function is lazily declared
        if (!(funcp->isMethod() && funcp->isLoose()) && !funcp->dpiImportPrototype()) return;
        // Already declared manually
        if (m_emittedManually.count(funcp->nameProtect())) return;
        // Needs lazy declaration, emit one
        m_emitter.emitCFuncDecl(funcp, EmitCParentModule::get(funcp), funcp->dpiImportPrototype());
        m_needsBlankLine = true;
    }

    void lazyDeclareConstPoolVar(AstVar* varp) {
        if (!declaredOnce(varp)) return;  // Already declared
        const string nameProtect
            = m_emitter.topClassName() + "__ConstPool__" + varp->nameProtect();
        m_emitter.puts("extern const ");
        m_emitter.puts(varp->dtypep()->cType(nameProtect, false, false));
        m_emitter.puts(";\n");
        m_needsBlankLine = true;
    }

    // VISITORS
    void visit(AstNodeCCall* nodep) override {
        lazyDeclare(nodep->funcp());
        iterateChildrenConst(nodep);
    }

    void visit(AstAddrOfCFunc* nodep) override {
        lazyDeclare(nodep->funcp());
        iterateChildrenConst(nodep);
    }

    void visit(AstVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        // Only constant pool symbols are lazy declared for now ...
        if (EmitCBase::isConstPoolMod(EmitCParentModule::get(varp))) {
            lazyDeclareConstPoolVar(varp);
        }
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit EmitCLazyDecls(EmitCBaseVisitorConst& emitter)
        : m_emitter(emitter) {}
    void emit(AstNode* nodep) {
        m_needsBlankLine = false;
        iterateChildrenConst(nodep);
        if (m_needsBlankLine) m_emitter.puts("\n");
    }
    void emit(const string& prefix, const string& name, const string& suffix) {
        m_emittedManually.insert(name);
        m_emitter.ensureNewLine();
        m_emitter.puts(prefix);
        m_emitter.puts(name);
        m_emitter.puts(suffix);
        m_emitter.ensureNewLine();
    }
    void declared(AstCFunc* nodep) { m_emitted.insert(nodep); }
    void reset() { m_emitted.clear(); }
};

// ######################################################################
//  Emit statements and expressions

class EmitCFunc VL_NOT_FINAL : public EmitCConstInit {
private:
    VMemberMap m_memberMap;
    AstVarRef* m_wideTempRefp = nullptr;  // Variable that _WW macros should be setting
    int m_labelNum = 0;  // Next label number
    int m_splitSize = 0;  // # of cfunc nodes placed into output file
    bool m_inUC = false;  // Inside an AstUCStmt or AstUCExpr
    bool m_emitConstInit = false;  // Emitting constant initializer

    // State associated with processing $display style string formatting
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
    } m_emitDispState;

protected:
    EmitCLazyDecls m_lazyDecls;  // Visitor for emitting lazy declarations
    bool m_useSelfForThis = false;  // Replace "this" with "vlSelf"
    const AstNodeModule* m_modp = nullptr;  // Current module being emitted
    const AstCFunc* m_cfuncp = nullptr;  // Current function being emitted
    bool m_instantiatesOwnProcess = false;

    bool constructorNeedsProcess(const AstClass* const classp) {
        const AstNode* const newp = m_memberMap.findMember(classp, "new");
        if (!newp) return false;
        const AstCFunc* const ctorp = VN_CAST(newp, CFunc);
        if (!ctorp) return false;
        UASSERT_OBJ(ctorp->isConstructor(), ctorp, "`new` is not a constructor!");
        return ctorp->needProcess();
    }

    bool constructorNeedsProcess(const AstNodeDType* const dtypep) {
        if (const AstClassRefDType* const crefdtypep = VN_CAST(dtypep, ClassRefDType))
            return constructorNeedsProcess(crefdtypep->classp());
        return false;
    }

public:
    // METHODS

    // ACCESSORS
    void splitSizeInc(int count) { m_splitSize += count; }
    void splitSizeInc(AstNode* nodep) { splitSizeInc(nodep->nodeCount()); }
    void splitSizeReset() { m_splitSize = 0; }
    bool splitNeeded() const {
        return v3Global.opt.outputSplit() && m_splitSize >= v3Global.opt.outputSplit();
    }

    // METHODS
    void displayNode(AstNode* nodep, AstScopeName* scopenamep, const string& vformat,
                     AstNode* exprsp, bool isScan);
    void displayEmit(AstNode* nodep, bool isScan);
    void displayArg(AstNode* dispp, AstNode** elistp, bool isScan, const string& vfmt, bool ignore,
                    char fmtLetter);

    bool emitSimpleOk(AstNodeExpr* nodep);
    void emitIQW(AstNode* nodep) {
        // Other abbrevs: "C"har, "S"hort, "F"loat, "D"ouble, stri"N"g
        puts(nodep->dtypep()->charIQWN());
    }
    void emitScIQW(AstVar* nodep) {
        UASSERT_OBJ(nodep->isSc(), nodep, "emitting SystemC operator on non-SC variable");
        puts(nodep->isScBigUint() ? "SB"
             : nodep->isScUint()  ? "SU"
             : nodep->isScBv()    ? "SW"
                                  : (nodep->isScQuad() ? "SQ" : "SI"));
    }
    void emitDatap(AstNode* nodep) {
        // When passing to a function with va_args the compiler doesn't
        // know need a pointer so when wide, need to look inside VlWide
        if (nodep->isWide()) puts(".data()");
    }
    void emitOpName(AstNode* nodep, const string& format, AstNode* lhsp, AstNode* rhsp,
                    AstNode* thsp);
    void emitCCallArgs(const AstNodeCCall* nodep, const string& selfPointer);
    void emitDereference(const string& pointer);
    void emitCvtPackStr(AstNode* nodep);
    void emitCvtWideArray(AstNode* nodep, AstNode* fromp);
    void emitConstant(AstConst* nodep, AstVarRef* assigntop, const string& assignString);
    void emitSetVarConstant(const string& assignString, AstConst* constp);
    void emitVarReset(AstVar* varp);
    string emitVarResetRecurse(const AstVar* varp, const string& varNameProtected,
                               AstNodeDType* dtypep, int depth, const string& suffix);
    void emitChangeDet();
    void emitConstInit(AstNode* initp) {
        // We should refactor emit to produce output into a provided buffer, not go through members
        // variables. That way we could just invoke the appropriate emitter as needed.
        VL_RESTORER(m_emitConstInit);
        m_emitConstInit = true;
        iterateConst(initp);
    }
    void putCommaIterateNext(AstNode* nodep, bool comma = false) {
        for (AstNode* subnodep = nodep; subnodep; subnodep = subnodep->nextp()) {
            if (comma) puts(", ");
            iterateConst(subnodep);
            comma = true;
        }
    }
    template <typename T>
    string optionalProcArg(const T* const nodep) {
        return (nodep && constructorNeedsProcess(nodep)) ? "vlProcess, " : "";
    }
    const AstCNew* getSuperNewCallRecursep(AstNode* const nodep) {
        // Get the super.new call
        if (!nodep) return nullptr;
        if (const AstCNew* const cnewp = VN_CAST(nodep, CNew)) return cnewp;
        if (const AstStmtExpr* const stmtp = VN_CAST(nodep, StmtExpr)) {
            if (const AstCNew* const cnewp = VN_CAST(stmtp->exprp(), CNew)) return cnewp;
        }
        if (const AstJumpBlock* const blockp = VN_CAST(nodep, JumpBlock)) {
            if (const AstCNew* const cnewp = getSuperNewCallRecursep(blockp->stmtsp())) {
                return cnewp;
            }
        }
        if (const AstCNew* const cnewp = getSuperNewCallRecursep(nodep->nextp())) return cnewp;
        return nullptr;
    }

    // VISITORS
    using EmitCConstInit::visit;
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_useSelfForThis);
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_instantiatesOwnProcess)
        m_cfuncp = nodep;
        m_instantiatesOwnProcess = false;

        splitSizeInc(nodep);

        puts("\n");
        m_lazyDecls.emit(nodep);
        if (nodep->ifdef() != "") puts("#ifdef " + nodep->ifdef() + "\n");
        if (nodep->isInline()) puts("VL_INLINE_OPT ");
        emitCFuncHeader(nodep, m_modp, /* withScope: */ true);

        if (!nodep->baseCtors().empty()) {
            puts(": ");
            puts(nodep->baseCtors());
            const AstClass* const classp = VN_CAST(nodep->scopep()->modp(), Class);
            // Find call to super.new to get the arguments
            if (classp && constructorNeedsProcess(classp)) {
                puts("(vlProcess, vlSymsp");
            } else {
                puts("(vlSymsp");
            }
            const AstCNew* const superNewCallp = getSuperNewCallRecursep(nodep->stmtsp());
            UASSERT_OBJ(superNewCallp, nodep, "super.new call not found");
            putCommaIterateNext(superNewCallp->argsp(), true);
            puts(")");
        }
        puts(" {\n");

        if (nodep->isLoose()) {
            m_lazyDecls.declared(nodep);  // Defined here, so no longer needs declaration
            if (!nodep->isStatic()) {  // Standard prologue
                m_useSelfForThis = true;
                puts("if (false && vlSelf) {}  // Prevent unused\n");
                if (!VN_IS(m_modp, Class)) puts(symClassAssign());
            }
        }

        // "+" in the debug indicates a print from the model
        puts("VL_DEBUG_IF(VL_DBG_MSGF(\"+  ");
        for (int i = 0; i < m_modp->level(); ++i) puts("  ");
        puts(prefixNameProtect(m_modp));
        puts(nodep->isLoose() ? "__" : "::");
        puts(nodep->nameProtect() + "\\n\"); );\n");

        // Instantiate a process class if it's going to be needed somewhere later
        nodep->forall([&](const AstNodeCCall* ccallp) -> bool {
            if (ccallp->funcp()->needProcess()
                && (ccallp->funcp()->isCoroutine() == VN_IS(ccallp->backp(), CAwait))) {
                if (!nodep->needProcess() && !m_instantiatesOwnProcess) {
                    m_instantiatesOwnProcess = true;
                    return false;
                }
            }
            return true;
        });
        if (m_instantiatesOwnProcess) {
            AstNode* const vlprocp = new AstCStmt{
                nodep->fileline(), "VlProcessRef vlProcess = std::make_shared<VlProcess>();\n"};
            nodep->stmtsp()->addHereThisAsNext(vlprocp);
        }

        for (AstNode* subnodep = nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
            if (AstVar* const varp = VN_CAST(subnodep, Var)) {
                if (varp->isFuncReturn()) emitVarDecl(varp);
            }
        }

        if (nodep->initsp()) {
            putsDecoration("// Init\n");
            iterateAndNextConstNull(nodep->initsp());
        }

        if (nodep->stmtsp()) {
            putsDecoration("// Body\n");
            iterateAndNextConstNull(nodep->stmtsp());
        }

        if (nodep->finalsp()) {
            putsDecoration("// Final\n");
            iterateAndNextConstNull(nodep->finalsp());
        }

        puts("}\n");
        if (nodep->ifdef() != "") puts("#endif  // " + nodep->ifdef() + "\n");
    }

    void visit(AstVar* nodep) override {
        UASSERT_OBJ(m_cfuncp, nodep, "Cannot emit non-local variable");
        emitVarDecl(nodep);
    }

    void visit(AstNodeAssign* nodep) override {
        bool paren = true;
        bool decind = false;
        bool rhs = true;
        if (AstSel* const selp = VN_CAST(nodep->lhsp(), Sel)) {
            if (selp->widthMin() == 1) {
                putbs("VL_ASSIGNBIT_");
                emitIQW(selp->fromp());
                if (nodep->rhsp()->isAllOnesV()) {
                    puts("O(");
                    rhs = false;
                } else {
                    puts("I(");
                }
                iterateAndNextConstNull(selp->lsbp());
                puts(", ");
                iterateAndNextConstNull(selp->fromp());
                if (rhs) puts(", ");
            } else {
                putbs("VL_ASSIGNSEL_");
                emitIQW(selp->fromp());
                emitIQW(nodep->rhsp());
                puts("(");
                puts(cvtToStr(selp->fromp()->widthMin()) + ",");
                puts(cvtToStr(nodep->widthMin()) + ",");
                iterateAndNextConstNull(selp->lsbp());
                puts(", ");
                iterateAndNextConstNull(selp->fromp());
                puts(", ");
            }
        } else if (const AstGetcRefN* const selp = VN_CAST(nodep->lhsp(), GetcRefN)) {
            iterateAndNextConstNull(selp->lhsp());
            puts(" = ");
            putbs("VL_PUTC_N(");
            iterateAndNextConstNull(selp->lhsp());
            puts(", ");
            iterateAndNextConstNull(selp->rhsp());
            puts(", ");
        } else if (AstVar* const varp = AstVar::scVarRecurse(nodep->lhsp())) {
            putbs("VL_ASSIGN_");  // Set a systemC variable
            emitScIQW(varp);
            emitIQW(nodep);
            puts("(");
            puts(cvtToStr(nodep->widthMin()) + ",");
            iterateAndNextConstNull(nodep->lhsp());
            puts(", ");
        } else if (AstVar* const varp = AstVar::scVarRecurse(nodep->rhsp())) {
            putbs("VL_ASSIGN_");  // Get a systemC variable
            emitIQW(nodep);
            emitScIQW(varp);
            puts("(");
            puts(cvtToStr(nodep->widthMin()) + ",");
            iterateAndNextConstNull(nodep->lhsp());
            puts(", ");
        } else if (const AstCvtPackedToDynArray* const castp
                   = VN_CAST(nodep->rhsp(), CvtPackedToDynArray)) {
            puts("VL_ASSIGN_DYN_Q<");
            putbs(castp->dtypep()->subDTypep()->cType("", false, false));
            puts(">(");
            iterateAndNextConstNull(nodep->lhsp());
            puts(", ");
            puts(cvtToStr(castp->dtypep()->subDTypep()->widthMin()));
            puts(", ");
            puts(cvtToStr(castp->fromp()->widthMin()));
            puts(", ");
            rhs = false;
            iterateAndNextConstNull(castp->fromp());
        } else if (nodep->isWide() && VN_IS(nodep->lhsp(), VarRef)  //
                   && !VN_IS(nodep->rhsp(), CExpr)  //
                   && !VN_IS(nodep->rhsp(), CMethodHard)  //
                   && !VN_IS(nodep->rhsp(), VarRef)  //
                   && !VN_IS(nodep->rhsp(), AssocSel)  //
                   && !VN_IS(nodep->rhsp(), MemberSel)  //
                   && !VN_IS(nodep->rhsp(), StructSel)  //
                   && !VN_IS(nodep->rhsp(), ArraySel)  //
                   && !VN_IS(nodep->rhsp(), ExprStmt)) {
            // Wide functions assign into the array directly, don't need separate assign statement
            m_wideTempRefp = VN_AS(nodep->lhsp(), VarRef);
            paren = false;
        } else if (nodep->isWide() && !VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType)) {
            putbs("VL_ASSIGN_W(");
            puts(cvtToStr(nodep->widthMin()) + ",");
            iterateAndNextConstNull(nodep->lhsp());
            puts(", ");
        } else {
            paren = false;
            iterateAndNextConstNull(nodep->lhsp());
            puts(" ");
            ofp()->blockInc();
            decind = true;
            if (!VN_IS(nodep->rhsp(), Const)) ofp()->putBreak();
            puts("= ");
        }
        if (rhs) iterateAndNextConstNull(nodep->rhsp());
        if (paren) puts(")");
        if (decind) ofp()->blockDec();
        puts(";\n");
    }
    void visit(AstAlwaysPublic*) override {}
    void visit(AstAssocSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        putbs(".at(");
        AstAssocArrayDType* const adtypep
            = VN_AS(nodep->fromp()->dtypep()->skipRefp(), AssocArrayDType);
        UASSERT_OBJ(adtypep, nodep, "Associative select on non-associative type");
        iterateAndNextConstNull(nodep->bitp());
        puts(")");
    }
    void visit(AstWildcardSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        putbs(".at(");
        AstWildcardArrayDType* const adtypep
            = VN_AS(nodep->fromp()->dtypep()->skipRefp(), WildcardArrayDType);
        UASSERT_OBJ(adtypep, nodep, "Wildcard select on non-wildcard-associative type");
        iterateAndNextConstNull(nodep->bitp());
        puts(")");
    }
    void visit(AstCCall* nodep) override {
        const AstCFunc* const funcp = nodep->funcp();
        const AstNodeModule* const funcModp = EmitCParentModule::get(funcp);
        if (funcp->dpiImportPrototype()) {
            // Calling DPI import
            puts(funcp->name());
        } else if (funcp->isProperMethod() && funcp->isStatic()) {
            // Call static method via the containing class
            puts(prefixNameProtect(funcModp) + "::");
            puts(funcp->nameProtect());
        } else if (VN_IS(funcModp, Class) && funcModp != m_modp) {
            // Calling superclass method
            puts(prefixNameProtect(funcModp) + "::");
            puts(funcp->nameProtect());
        } else if (funcp->isLoose()) {
            // Calling loose method
            puts(funcNameProtect(funcp));
        } else {
            // Calling regular method/function
            if (!nodep->selfPointer().empty()) {
                emitDereference(nodep->selfPointerProtect(m_useSelfForThis));
            }
            puts(funcp->nameProtect());
        }
        emitCCallArgs(nodep, nodep->selfPointerProtect(m_useSelfForThis));
    }
    void visit(AstCMethodCall* nodep) override {
        const AstCFunc* const funcp = nodep->funcp();
        UASSERT_OBJ(!funcp->isLoose(), nodep, "Loose method called via AstCMethodCall");
        iterateConst(nodep->fromp());
        putbs("->");
        puts(funcp->nameProtect());
        emitCCallArgs(nodep, "");
    }
    void visit(AstCAwait* nodep) override {
        puts("co_await ");
        iterateConst(nodep->exprp());
    }
    void visit(AstCNew* nodep) override {
        if (VN_IS(nodep->dtypep(), VoidDType)) {
            // super.new case
            return;
        }
        // assignment case;
        puts("VL_NEW(" + prefixNameProtect(nodep->dtypep()) + ", "
             + optionalProcArg(nodep->dtypep()) + "vlSymsp");
        putCommaIterateNext(nodep->argsp(), true);
        puts(")");
    }
    void visit(AstCMethodHard* nodep) override {
        iterateConst(nodep->fromp());
        puts(".");
        puts(nodep->name());
        puts("(");
        bool comma = false;
        for (AstNode* subnodep = nodep->pinsp(); subnodep; subnodep = subnodep->nextp()) {
            if (comma) puts(", ");
            // handle wide arguments to the queues
            if (VN_IS(nodep->fromp()->dtypep(), QueueDType) && subnodep->dtypep()->isWide()) {
                emitCvtWideArray(subnodep, nodep->fromp());
            } else {
                iterateConst(subnodep);
            }
            comma = true;
        }
        puts(")");
    }
    void visit(AstLambdaArgRef* nodep) override { putbs(nodep->nameProtect()); }
    void visit(AstWith* nodep) override {
        // With uses a C++11 lambda
        putbs("[&](");
        if (auto* const argrefp = nodep->indexArgRefp()) {
            putbs(argrefp->dtypep()->cType(argrefp->nameProtect(), false, false));
            puts(",");
        }
        if (auto* const argrefp = nodep->valueArgRefp()) {
            putbs(argrefp->dtypep()->cType(argrefp->nameProtect(), false, false));
        }
        puts(") {\n");
        iterateAndNextConstNull(nodep->exprp());
        puts("}\n");
    }
    void visit(AstNodeCase* nodep) override {  // LCOV_EXCL_LINE
        // In V3Case...
        nodep->v3fatalSrc("Case statements should have been reduced out");
    }
    void visit(AstComment* nodep) override {
        string at;
        if (nodep->showAt()) {
            at = " at " + nodep->fileline()->ascii();
            // If protecting, passthru less information about the design
            if (!v3Global.opt.protectIds()) return;
        }
        if (!(nodep->protect() && v3Global.opt.protectIds())) {
            putsDecoration(string{"// "} + nodep->name() + at + "\n");
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstCoverDecl* nodep) override {
        puts("vlSelf->__vlCoverInsert(");  // As Declared in emitCoverageDecl
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
    void visit(AstCoverInc* nodep) override {
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
    void visit(AstCReturn* nodep) override {
        puts("return (");
        iterateAndNextConstNull(nodep->lhsp());
        puts(");\n");
    }
    void visit(AstDisplay* nodep) override {
        string text = nodep->fmtp()->text();
        if (nodep->addNewline()) text += "\n";
        displayNode(nodep, nodep->fmtp()->scopeNamep(), text, nodep->fmtp()->exprsp(), false);
    }
    void visit(AstDumpCtl* nodep) override {
        switch (nodep->ctlType()) {
        case VDumpCtlType::FILE:
            puts("vlSymsp->_vm_contextp__->dumpfile(");
            emitCvtPackStr(nodep->exprp());
            puts(");\n");
            break;
        case VDumpCtlType::VARS:
            // We ignore number of levels to dump in exprp()
            if (v3Global.opt.trace()) {
                puts("vlSymsp->_traceDumpOpen();\n");
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
    void visit(AstScopeName* nodep) override {
        // For use under AstCCalls for dpiImports.  ScopeNames under
        // displays are handled in AstDisplay
        if (!nodep->dpiExport()) {
            // this is where the DPI import context scope is set
            const string scope = nodep->scopeDpiName();
            putbs("(&(vlSymsp->" + protect("__Vscope_" + scope) + "))");
        }
    }
    void visit(AstSFormat* nodep) override {
        displayNode(nodep, nodep->fmtp()->scopeNamep(), nodep->fmtp()->text(),
                    nodep->fmtp()->exprsp(), false);
    }
    void visit(AstSFormatF* nodep) override {
        displayNode(nodep, nodep->scopeNamep(), nodep->text(), nodep->exprsp(), false);
    }
    void visit(AstFScanF* nodep) override {
        displayNode(nodep, nullptr, nodep->text(), nodep->exprsp(), true);
    }
    void visit(AstSScanF* nodep) override {
        displayNode(nodep, nullptr, nodep->text(), nodep->exprsp(), true);
    }
    void visit(AstValuePlusArgs* nodep) override {
        puts("VL_VALUEPLUSARGS_IN");
        emitIQW(nodep->outp());
        puts("(");
        puts(cvtToStr(nodep->outp()->widthMin()));
        puts(", ");
        emitCvtPackStr(nodep->searchp());
        puts(", ");
        putbs("");
        iterateAndNextConstNull(nodep->outp());
        puts(")");
    }
    void visit(AstTestPlusArgs* nodep) override {
        puts("VL_TESTPLUSARGS_I(");
        emitCvtPackStr(nodep->searchp());
        puts(")");
    }
    void visit(AstFError* nodep) override {
        puts("VL_FERROR_I");
        puts(nodep->strp()->isString() ? "N(" : "W(");
        iterateAndNextConstNull(nodep->filep());
        putbs(", ");
        if (nodep->strp()->isWide()) {
            puts(cvtToStr(nodep->strp()->widthWords()));
            putbs(", ");
        }
        iterateAndNextConstNull(nodep->strp());
        puts(")");
    }
    void visit(AstFGetS* nodep) override {
        checkMaxWords(nodep);
        emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nullptr);
    }

    void checkMaxWords(AstNode* nodep) {
        if (nodep->widthWords() > VL_VALUE_STRING_MAX_WORDS) {
            nodep->v3error(
                "String of "
                << nodep->width()
                << " bits exceeds hardcoded limit VL_VALUE_STRING_MAX_WORDS in verilatedos.h");
        }
    }
    void visit(AstFOpen* nodep) override {
        puts("VL_FOPEN_NN(");
        emitCvtPackStr(nodep->filenamep());
        putbs(", ");
        if (nodep->modep()->width() > 4 * 8)
            nodep->modep()->v3error("$fopen mode should be <= 4 characters");
        emitCvtPackStr(nodep->modep());
        puts(");\n");
    }
    void visit(AstFOpenMcd* nodep) override {
        puts("VL_FOPEN_MCD_N(");
        emitCvtPackStr(nodep->filenamep());
        puts(");\n");
    }
    void visit(AstNodeReadWriteMem* nodep) override {
        puts(nodep->cFuncPrefixp());
        puts("N(");
        puts(nodep->isHex() ? "true" : "false");
        putbs(", ");
        // Need real storage width
        puts(cvtToStr(nodep->memp()->dtypep()->subDTypep()->widthMin()));
        uint32_t array_lo = 0;
        {
            const AstVarRef* const varrefp = VN_CAST(nodep->memp(), VarRef);
            if (!varrefp) {
                nodep->v3error(nodep->verilogKwd() << " loading non-variable");
            } else if (VN_IS(varrefp->varp()->dtypeSkipRefp(), AssocArrayDType)) {
                // nodep->memp() below will when verilated code is compiled create a C++ template
            } else if (const AstUnpackArrayDType* const adtypep
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
            iterateAndNextConstNull(nodep->memp());
            if (need_ptr) puts(")");
        }
        putbs(", ");
        if (nodep->lsbp()) {
            iterateAndNextConstNull(nodep->lsbp());
        } else {
            puts(cvtToStr(array_lo));
        }
        putbs(", ");
        if (nodep->msbp()) {
            iterateAndNextConstNull(nodep->msbp());
        } else {
            puts("~0ULL");
        }
        puts(");\n");
    }
    void visit(AstFClose* nodep) override {
        puts("VL_FCLOSE_I(");
        iterateAndNextConstNull(nodep->filep());
        puts("); ");
    }
    void visit(AstFFlush* nodep) override {
        if (!nodep->filep()) {
            puts("Verilated::runFlushCallbacks();\n");
        } else {
            puts("if (");
            iterateAndNextConstNull(nodep->filep());
            puts(") { VL_FFLUSH_I(");
            iterateAndNextConstNull(nodep->filep());
            puts("); }\n");
        }
    }
    void visit(AstFSeek* nodep) override {
        puts("(VL_FSEEK_I(");
        iterateAndNextConstNull(nodep->filep());
        puts(",");
        iterateAndNextConstNull(nodep->offset());
        puts(",");
        iterateAndNextConstNull(nodep->operation());
        puts(") == -1 ? -1 : 0)");
    }
    void visit(AstFTell* nodep) override {
        puts("VL_FTELL_I(");
        iterateAndNextConstNull(nodep->filep());
        puts(")");
    }
    void visit(AstFRewind* nodep) override {
        puts("(VL_FSEEK_I(");
        iterateAndNextConstNull(nodep->filep());
        puts(", 0, 0) == -1 ? -1 : 0)");
    }
    void visit(AstFRead* nodep) override {
        puts("VL_FREAD_I(");
        puts(cvtToStr(nodep->memp()->widthMin()));  // Need real storage width
        putbs(",");
        uint32_t array_lo = 0;
        uint32_t array_size = 0;
        {
            const AstVarRef* const varrefp = VN_CAST(nodep->memp(), VarRef);
            if (!varrefp) {
                nodep->v3error(nodep->verilogKwd() << " loading non-variable");
            } else if (VN_CAST(varrefp->varp()->dtypeSkipRefp(), BasicDType)) {
            } else if (const AstUnpackArrayDType* const adtypep
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
        iterateAndNextConstNull(nodep->memp());
        puts(")");
        putbs(", ");
        iterateAndNextConstNull(nodep->filep());
        putbs(", ");
        if (nodep->startp()) {
            iterateAndNextConstNull(nodep->startp());
        } else {
            puts(cvtToStr(array_lo));
        }
        putbs(", ");
        if (nodep->countp()) {
            iterateAndNextConstNull(nodep->countp());
        } else {
            puts(cvtToStr(array_size));
        }
        puts(")");
    }
    void visit(AstSysFuncAsTask* nodep) override {
        if (!nodep->lhsp()->isWide()) puts("(void)");
        iterateAndNextConstNull(nodep->lhsp());
        if (!nodep->lhsp()->isWide()) puts(";\n");
    }
    void visit(AstStackTraceF* nodep) override { puts("VL_STACKTRACE_N()"); }
    void visit(AstStackTraceT* nodep) override { puts("VL_STACKTRACE();\n"); }
    void visit(AstSystemT* nodep) override {
        puts("(void)VL_SYSTEM_I");
        emitIQW(nodep->lhsp());
        puts("(");
        if (nodep->lhsp()->isWide()) {
            puts(cvtToStr(nodep->lhsp()->widthWords()));
            putbs(", ");
        }
        checkMaxWords(nodep->lhsp());
        iterateAndNextConstNull(nodep->lhsp());
        puts(");\n");
    }
    void visit(AstSystemF* nodep) override {
        puts("VL_SYSTEM_I");
        emitIQW(nodep->lhsp());
        puts("(");
        if (nodep->lhsp()->isWide()) {
            puts(cvtToStr(nodep->lhsp()->widthWords()));
            putbs(", ");
        }
        checkMaxWords(nodep->lhsp());
        iterateAndNextConstNull(nodep->lhsp());
        puts(")");
    }
    void visit(AstStmtExpr* node) override {
        iterateConst(node->exprp());
        puts(";\n");
    }
    void visit(AstJumpBlock* nodep) override {
        nodep->labelNum(++m_labelNum);
        puts("{\n");  // Make it visually obvious label jumps outside these
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->endStmtsp());
        puts("}\n");
    }
    void visit(AstCLocalScope* nodep) override {
        puts("{\n");
        iterateAndNextConstNull(nodep->stmtsp());
        puts("}\n");
    }
    void visit(AstJumpGo* nodep) override {
        puts("goto __Vlabel" + cvtToStr(nodep->labelp()->blockp()->labelNum()) + ";\n");
    }
    void visit(AstJumpLabel* nodep) override {
        puts("__Vlabel" + cvtToStr(nodep->blockp()->labelNum()) + ": ;\n");
    }
    void visit(AstWhile* nodep) override {
        iterateAndNextConstNull(nodep->precondsp());
        puts("while (");
        iterateAndNextConstNull(nodep->condp());
        puts(") {\n");
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->incsp());
        iterateAndNextConstNull(nodep->precondsp());  // Need to recompute before next loop
        puts("}\n");
    }
    void visit(AstNodeIf* nodep) override {
        puts("if (");
        if (!nodep->branchPred().unknown()) {
            puts(nodep->branchPred().ascii());
            puts("(");
        }
        iterateAndNextConstNull(nodep->condp());
        if (!nodep->branchPred().unknown()) puts(")");
        puts(") {\n");
        iterateAndNextConstNull(nodep->thensp());
        puts("}");
        if (!nodep->elsesp()) {
            puts("\n");
        } else {
            if (VN_IS(nodep->elsesp(), NodeIf) && !nodep->elsesp()->nextp()) {
                puts(" else ");
                iterateAndNextConstNull(nodep->elsesp());
            } else {
                puts(" else {\n");
                iterateAndNextConstNull(nodep->elsesp());
                puts("}\n");
            }
        }
    }
    void visit(AstExprStmt* nodep) override {
        // GCC allows compound statements in expressions, but this is not standard.
        // So we use an immediate-evaluation lambda and comma operator
        putbs("([&]() {\n");
        iterateAndNextConstNull(nodep->stmtsp());
        puts("}(), ");
        iterateAndNextConstNull(nodep->resultp());
        puts(")");
    }
    void visit(AstStop* nodep) override {
        puts("VL_STOP_MT(");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(", \"\"");
        puts(");\n");
    }
    void visit(AstFinish* nodep) override {
        puts("VL_FINISH_MT(");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(", \"\");\n");
    }
    void visit(AstPrintTimeScale* nodep) override {
        puts("VL_PRINTTIMESCALE(");
        putsQuoted(protect(nodep->prettyName()));
        puts(", ");
        putsQuoted(nodep->timeunit().ascii());
        puts(", vlSymsp->_vm_contextp__);\n");
    }
    void visit(AstRand* nodep) override {
        emitOpName(nodep, nodep->emitC(), nodep->seedp(), nullptr, nullptr);
    }
    void visit(AstRandRNG* nodep) override {
        emitOpName(nodep, nodep->emitC(), nullptr, nullptr, nullptr);
    }
    void visit(AstTime* nodep) override {
        puts("VL_TIME_UNITED_Q(");
        if (nodep->timeunit().isNone()) nodep->v3fatalSrc("$time has no units");
        puts(cvtToStr(nodep->timeunit().multiplier()
                      / v3Global.rootp()->timeprecision().multiplier()));
        puts(")");
    }
    void visit(AstTimeD* nodep) override {
        puts("VL_TIME_UNITED_D(");
        if (nodep->timeunit().isNone()) nodep->v3fatalSrc("$realtime has no units");
        puts(cvtToStr(nodep->timeunit().multiplier()
                      / v3Global.rootp()->timeprecision().multiplier()));
        puts(")");
    }
    void visit(AstTimeFormat* nodep) override {
        puts("VL_TIMEFORMAT_IINI(");
        iterateAndNextConstNull(nodep->unitsp());
        puts(", ");
        iterateAndNextConstNull(nodep->precisionp());
        puts(", ");
        emitCvtPackStr(nodep->suffixp());
        puts(", ");
        iterateAndNextConstNull(nodep->widthp());
        puts(", vlSymsp->_vm_contextp__);\n");
    }
    void visit(AstTimePrecision* nodep) override {
        puts("vlSymsp->_vm_contextp__->timeprecision()");
    }
    void visit(AstNodeSimpleText* nodep) override {
        const string text = m_inUC && m_useSelfForThis
                                ? VString::replaceWord(nodep->text(), "this", "vlSelf")
                                : nodep->text();
        if (nodep->tracking() || m_trackText) {
            puts(text);
        } else {
            ofp()->putsNoTracking(text);
        }
    }
    void visit(AstTextBlock* nodep) override {
        visit(static_cast<AstNodeSimpleText*>(nodep));
        for (AstNode* childp = nodep->nodesp(); childp; childp = childp->nextp()) {
            iterateConst(childp);
            if (nodep->commas() && childp->nextp()) puts(", ");
        }
    }
    void visit(AstCStmt* nodep) override {
        putbs("");
        iterateAndNextConstNull(nodep->exprsp());
    }
    void visit(AstCExpr* nodep) override {
        putbs("");
        iterateAndNextConstNull(nodep->exprsp());
    }
    void visit(AstUCStmt* nodep) override {
        VL_RESTORER(m_inUC);
        m_inUC = true;
        putsDecoration(ifNoProtect("// $c statement at " + nodep->fileline()->ascii() + "\n"));
        iterateAndNextConstNull(nodep->exprsp());
        puts("\n");
    }
    void visit(AstUCFunc* nodep) override {
        VL_RESTORER(m_inUC);
        m_inUC = true;
        puts("\n");
        putsDecoration(ifNoProtect("// $c function at " + nodep->fileline()->ascii() + "\n"));
        iterateAndNextConstNull(nodep->exprsp());
        puts("\n");
    }

    // Operators
    void visit(AstNodeTermop* nodep) override {
        emitOpName(nodep, nodep->emitC(), nullptr, nullptr, nullptr);
    }
    void visit(AstNodeUniop* nodep) override {
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
            iterateAndNextConstNull(nodep->lhsp());
            puts(")");
        } else {
            emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nullptr, nullptr);
        }
    }
    void visit(AstNodeBiop* nodep) override {
        if (nodep->emitCheckMaxWords() && nodep->widthWords() > VL_MULS_MAX_WORDS) {
            nodep->v3warn(
                E_UNSUPPORTED,
                "Unsupported: "
                    << nodep->prettyOperatorName() << " operator of " << nodep->width()
                    << " bits exceeds hardcoded limit VL_MULS_MAX_WORDS in verilatedos.h");
        }
        if (emitSimpleOk(nodep)) {
            putbs("(");
            iterateAndNextConstNull(nodep->lhsp());
            puts(" ");
            putbs(nodep->emitSimpleOperator());
            puts(" ");
            iterateAndNextConstNull(nodep->rhsp());
            puts(")");
        } else {
            emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nullptr);
        }
    }
    void visit(AstNodeTriop* nodep) override {
        UASSERT_OBJ(!emitSimpleOk(nodep), nodep, "Triop cannot be described in a simple way");
        emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nodep->thsp());
    }
    void visit(AstCvtPackString* nodep) override { emitCvtPackStr(nodep->lhsp()); }
    void visit(AstRedXor* nodep) override {
        if (nodep->lhsp()->isWide()) {
            visit(static_cast<AstNodeUniop*>(nodep));
        } else {
            const AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef);
            const int widthPow2 = vrefp ? vrefp->varp()->dtypep()->widthPow2()
                                        : nodep->lhsp()->dtypep()->widthPow2();
            UASSERT_OBJ(widthPow2 > 1, nodep,
                        "Reduction over single bit value should have been folded");
            putbs("VL_REDXOR_");
            puts(cvtToStr(widthPow2));
            puts("(");
            iterateAndNextConstNull(nodep->lhsp());
            puts(")");
        }
    }
    void visit(AstCCast* nodep) override {
        // Extending a value of the same word width is just a NOP.
        if (const AstClassRefDType* const classDtypep = VN_CAST(nodep->dtypep(), ClassRefDType)) {
            puts("(" + classDtypep->cType("", false, false) + ")(");
        } else if (nodep->size() <= VL_IDATASIZE) {
            puts("(IData)(");
        } else {
            puts("(QData)(");
        }
        iterateAndNextConstNull(nodep->lhsp());
        puts(")");
    }
    void visit(AstNodeCond* nodep) override {
        // Widths match up already, so we'll just use C++'s operator w/o any temps.
        if (nodep->thenp()->isWide()) {
            emitOpName(nodep, nodep->emitC(), nodep->condp(), nodep->thenp(), nodep->elsep());
        } else {
            putbs("(");
            iterateAndNextConstNull(nodep->condp());
            putbs(" ? ");
            iterateAndNextConstNull(nodep->thenp());
            putbs(" : ");
            iterateAndNextConstNull(nodep->elsep());
            puts(")");
        }
    }
    void visit(AstMemberSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        putbs("->");
        puts(nodep->varp()->nameProtect());
    }
    void visit(AstStructSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        putbs(".");
        puts(nodep->nameProtect());
    }
    void visit(AstNullCheck* nodep) override {
        puts("VL_NULL_CHECK(");
        iterateAndNextConstNull(nodep->lhsp());
        puts(", ");
        putsQuoted(protect(nodep->fileline()->filename()));
        puts(", ");
        puts(cvtToStr(nodep->fileline()->lineno()));
        puts(")");
    }
    void visit(AstNewCopy* nodep) override {
        puts("VL_NEW(" + prefixNameProtect(nodep->dtypep()) + ", "
             + optionalProcArg(nodep->dtypep()));
        puts("*");  // i.e. make into a reference
        iterateAndNextConstNull(nodep->rhsp());
        puts(")");
    }
    void visit(AstSel* nodep) override {
        // Note ASSIGN checks for this on a LHS
        emitOpName(nodep, nodep->emitC(), nodep->fromp(), nodep->lsbp(), nodep->thsp());
    }
    void visit(AstReplicate* nodep) override {
        if (nodep->lhsp()->widthMin() == 1 && !nodep->isWide()) {
            UASSERT_OBJ((static_cast<int>(VN_AS(nodep->rhsp(), Const)->toUInt())
                         * nodep->lhsp()->widthMin())
                            == nodep->widthMin(),
                        nodep, "Replicate non-constant or width miscomputed");
            puts("VL_REPLICATE_");
            emitIQW(nodep);
            puts("OI(");
            if (nodep->lhsp()) puts(cvtToStr(nodep->lhsp()->widthMin()));
            puts(",");
            iterateAndNextConstNull(nodep->lhsp());
            puts(", ");
            iterateAndNextConstNull(nodep->rhsp());
            puts(")");
        } else {
            emitOpName(nodep, nodep->emitC(), nodep->lhsp(), nodep->rhsp(), nullptr);
        }
    }
    void visit(AstStreamL* nodep) override {
        // Attempt to use a "fast" stream function for slice size = power of 2
        if (!nodep->isWide()) {
            const uint32_t isPow2 = VN_AS(nodep->rhsp(), Const)->num().countOnes() == 1;
            const uint32_t sliceSize = VN_AS(nodep->rhsp(), Const)->toUInt();
            if (isPow2 && sliceSize <= (nodep->isQuad() ? sizeof(uint64_t) : sizeof(uint32_t))) {
                puts("VL_STREAML_FAST_");
                emitIQW(nodep);
                emitIQW(nodep->lhsp());
                puts("I(");
                puts(cvtToStr(nodep->lhsp()->widthMin()));
                puts(", ");
                iterateAndNextConstNull(nodep->lhsp());
                puts(", ");
                const uint32_t rd_log2 = V3Number::log2b(VN_AS(nodep->rhsp(), Const)->toUInt());
                puts(cvtToStr(rd_log2) + ")");
                return;
            }
        }
        emitOpName(nodep, "VL_STREAML_%nq%lq%rq(%lw, %P, %li, %ri)", nodep->lhsp(), nodep->rhsp(),
                   nullptr);
    }
    void visit(AstCastDynamic* nodep) override {
        putbs("VL_CAST_DYNAMIC(");
        iterateAndNextConstNull(nodep->lhsp());
        puts(", ");
        iterateAndNextConstNull(nodep->rhsp());
        puts(")");
    }
    void visit(AstCountBits* nodep) override {
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
        iterateAndNextConstNull(nodep->lhsp());
        puts(", ");
        iterateAndNextConstNull(nodep->rhsp());
        puts(", ");
        iterateAndNextConstNull(nodep->thsp());
        puts(", ");
        iterateAndNextConstNull(nodep->fhsp());
        puts(")");
    }
    void visit(AstInitItem* nodep) override { iterateChildrenConst(nodep); }
    // Terminals
    void visit(AstVarRef* nodep) override {
        const AstVar* const varp = nodep->varp();
        const AstNodeModule* const varModp = EmitCParentModule::get(varp);
        if (isConstPoolMod(varModp)) {
            // Reference to constant pool variable
            puts(topClassName() + "__ConstPool__");
        } else if (varp->isStatic()) {
            // Access static variable via the containing class
            puts(prefixNameProtect(varModp) + "::");
        } else if (VN_IS(varModp, Class) && varModp != m_modp) {
            // Superclass member reference
            puts(prefixNameProtect(varModp) + "::");
        } else if (varp->isIfaceRef()) {
            puts(nodep->selfPointerProtect(m_useSelfForThis));
            return;
        } else if (!nodep->selfPointer().empty()) {
            emitDereference(nodep->selfPointerProtect(m_useSelfForThis));
        }
        puts(nodep->varp()->nameProtect());
    }
    void visit(AstAddrOfCFunc* nodep) override {
        // Note: Can be thought to handle more, but this is all that is needed right now
        const AstCFunc* const funcp = nodep->funcp();
        UASSERT_OBJ(funcp->isLoose(), nodep, "Cannot take address of non-loose method");
        puts("&");
        puts(funcNameProtect(funcp));
    }
    void visit(AstConst* nodep) override {
        if (m_emitConstInit) {
            EmitCConstInit::visit(nodep);
        } else if (nodep->isWide()) {
            UASSERT_OBJ(m_wideTempRefp, nodep, "Wide Constant w/ no temp");
            emitConstant(nodep, m_wideTempRefp, "");
            m_wideTempRefp = nullptr;  // We used it, fail if set it a second time
        } else {
            emitConstant(nodep, nullptr, "");
        }
    }
    void visit(AstThisRef* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        puts("{");
        puts(m_useSelfForThis ? "vlSelf" : "this");
        puts("}");
    }

    //
    void visit(AstMTaskBody* nodep) override {
        VL_RESTORER(m_useSelfForThis);
        m_useSelfForThis = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstConsAssoc* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        puts("()");
        if (nodep->defaultp()) {
            putbs(".setDefault(");
            iterateAndNextConstNull(nodep->defaultp());
            puts(")");
        }
    }
    void visit(AstSetAssoc* nodep) override {
        iterateAndNextConstNull(nodep->lhsp());
        putbs(".set(");
        iterateAndNextConstNull(nodep->keyp());
        puts(", ");
        putbs("");
        iterateAndNextConstNull(nodep->valuep());
        puts(")");
    }
    void visit(AstConsWildcard* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        puts("()");
        if (nodep->defaultp()) {
            putbs(".setDefault(");
            iterateAndNextConstNull(nodep->defaultp());
            puts(")");
        }
    }
    void visit(AstSetWildcard* nodep) override {
        iterateAndNextConstNull(nodep->lhsp());
        putbs(".set(");
        iterateAndNextConstNull(nodep->keyp());
        puts(", ");
        putbs("");
        iterateAndNextConstNull(nodep->valuep());
        puts(")");
    }
    void visit(AstConsDynArray* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        if (!nodep->lhsp()) {
            puts("()");
        } else {
            puts("::cons(");
            iterateAndNextConstNull(nodep->lhsp());
            if (nodep->rhsp()) {
                puts(", ");
                putbs("");
            }
            iterateAndNextConstNull(nodep->rhsp());
            puts(")");
        }
    }
    void visit(AstConsPackUOrStruct* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        puts("{");
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            iterateConst(memberp);
            if (memberp->nextp()) { puts(", "); }
        }
        puts("}");
    }
    void visit(AstConsPackMember* nodep) override {
        auto* const vdtypep = VN_AS(nodep->dtypep(), MemberDType);
        putbs(".");
        puts(vdtypep->name());
        puts(" = ");
        iterateConst(nodep->rhsp());
    }
    void visit(AstConsQueue* nodep) override {
        putbs(nodep->dtypep()->cType("", false, false));
        if (!nodep->lhsp()) {
            puts("()");
        } else {
            puts("::cons(");
            iterateAndNextConstNull(nodep->lhsp());
            if (nodep->rhsp()) {
                puts(", ");
                putbs("");
            }
            iterateAndNextConstNull(nodep->rhsp());
            puts(")");
        }
    }
    void visit(AstCReset* nodep) override {
        AstVar* const varp = nodep->varrefp()->varp();
        emitVarReset(varp);
    }
    void visit(AstExecGraph* nodep) override {
        // The location of the AstExecGraph within the containing AstCFunc is where we want to
        // invoke the graph and wait for it to complete. Emitting the children does just that.
        UASSERT_OBJ(!nodep->mTaskBodiesp(), nodep, "These should have been lowered");
        iterateChildrenConst(nodep);
    }

    // Default
    void visit(AstNode* nodep) override {
        puts(string{"\n???? // "} + nodep->prettyTypeName() + "\n");
        iterateChildrenConst(nodep);
        // LCOV_EXCL_START
        if (!v3Global.opt.lintOnly()) {  // An internal problem, so suppress
            nodep->v3fatalSrc("Unknown node type reached emitter: " << nodep->prettyTypeName());
        }
        // LCOV_EXCL_STOP
    }

    EmitCFunc()
        : m_lazyDecls(*this) {}
    EmitCFunc(AstNode* nodep, V3OutCFile* ofp, bool trackText = false)
        : EmitCFunc{} {
        m_ofp = ofp;
        m_trackText = trackText;
        iterateConst(nodep);
    }
    ~EmitCFunc() override = default;
};

#endif  // guard
