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

#include "V3PchAstMT.h"

#include "V3EmitCFunc.h"

#include "V3TSP.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// EmitCFunc

bool EmitCFunc::emitSimpleOk(AstNodeExpr* nodep) {
    // Can we put out a simple (A + B) instead of VL_ADD_III(A,B)?
    if (nodep->emitSimpleOperator() == "") return false;
    if (nodep->isWide()) return false;
    if (nodep->op1p() && nodep->op1p()->isWide()) return false;
    if (nodep->op2p() && nodep->op2p()->isWide()) return false;
    if (nodep->op3p() && nodep->op3p()->isWide()) return false;
    return true;
}

void EmitCFunc::emitOpName(AstNode* nodep, const string& format, AstNode* lhsp, AstNode* rhsp,
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
    string out;
    putnbs(nodep, "");

    bool needComma = false;
    string nextComma;
    auto commaOut = [&out, &nextComma]() {
        if (!nextComma.empty()) {
            out += nextComma;
            nextComma = "";
        }
    };

    auto putOut = [this, &out]() {
        if (!out.empty()) puts(out);
        out = "";
    };

    for (string::const_iterator pos = format.begin(); pos != format.end(); ++pos) {
        if (pos[0] == ',') {
            // Remember we need to add one, but don't do yet to avoid ",)"
            if (needComma) {
                if (pos[1] == ' ') {
                    nextComma = ", ";
                } else {
                    nextComma = ",";
                }
                needComma = false;
            }
            if (pos[1] == ' ') ++pos;  // Must do even if no nextComma
        } else if (pos[0] == '%') {
            ++pos;
            bool detail = false;
            AstNode* detailp = nullptr;
            switch (pos[0]) {
            case '%': out += '%'; break;
            case 'k':
                putOut();
                putbs("");
                break;
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
                    commaOut();
                    putOut();
                    if (!m_wideTempRefp->selfPointer().isEmpty()) {
                        emitDereference(m_wideTempRefp,
                                        m_wideTempRefp->selfPointerProtect(m_useSelfForThis));
                    }
                    out += m_wideTempRefp->varp()->nameProtect();
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
                case 'q':
                    putOut();
                    emitIQW(detailp);
                    break;
                case 'w':
                    commaOut();
                    out += cvtToStr(detailp->widthMin());
                    needComma = true;
                    break;
                case 'W':
                    if (lhsp->isWide()) {
                        commaOut();
                        out += cvtToStr(lhsp->widthWords());
                        needComma = true;
                    }
                    break;
                case 'i':
                    commaOut();
                    UASSERT_OBJ(detailp, nodep, "emitOperator() references undef node");
                    putOut();
                    iterateAndNextConstNull(detailp);
                    needComma = true;
                    break;
                default:
                    nodep->v3fatalSrc("Unknown emitOperator format code: %[nlrt]" << pos[0]);
                    break;
                }
            }
        } else if (pos[0] == ')') {
            nextComma = "";
            out += ')';
        } else if (pos[0] == '(') {
            commaOut();
            needComma = false;
            out += '(';
        } else {
            // Normal text
            if (std::isalnum(pos[0])) needComma = true;
            commaOut();
            out += pos[0];
        }
    }
    putOut();
}

bool EmitCFunc::displayEmitHeader(AstNode* nodep) {
    bool isStmt = false;
    if (const AstFScanF* const dispp = VN_CAST(nodep, FScanF)) {
        isStmt = false;
        putns(nodep, "VL_FSCANF_INX(");
        iterateConst(dispp->filep());
        puts(",");
    } else if (const AstSScanF* const dispp = VN_CAST(nodep, SScanF)) {
        isStmt = false;
        putns(nodep, "VL_SSCANF_I");
        emitIQW(dispp->fromp());
        puts("NX(");
        puts(cvtToStr(dispp->fromp()->widthMin()));
        puts(",");
        iterateConst(dispp->fromp());
        puts(",");
    } else if (const AstDisplay* const dispp = VN_CAST(nodep, Display)) {
        isStmt = true;
        if (dispp->filep()) {
            putns(nodep, "VL_FWRITEF_NX(");
            iterateConst(dispp->filep());
            puts(",");
        } else {
            putns(nodep, "VL_WRITEF_NX(");
        }
    } else if (const AstSFormat* const dispp = VN_CAST(nodep, SFormat)) {
        isStmt = true;
        puts("VL_SFORMAT_NX(");
        puts(cvtToStr(dispp->lhsp()->widthMin()));
        putbs(",");
        iterateConst(dispp->lhsp());
        putbs(",");
    } else if (VN_IS(nodep, SFormatF)) {
        isStmt = false;
        putns(nodep, "VL_SFORMATF_N_NX(");
    } else {
        nodep->v3fatalSrc("Unknown displayEmit node type");
    }
    return isStmt;
}

void EmitCFunc::displayNode(AstNode* nodep, AstSFormatF* fmtp,  // fmtp is nullptr for AstScan
                            const string& vformat, AstNode* exprsp, bool isScan) {
    // Check format, if it exists
    const bool exprFormat = fmtp && fmtp->exprFormat();
    bool needsScope = exprFormat;
    bool needsTimescale = exprFormat;
    int formatArgs = 0;
    if (!exprFormat) {
        // Check display and argument count to head-off later runtime issues
        bool inPct = false;
        bool ignore = false;
        for (char ch : vformat) {
            // UINFO(1, "Parse '" << *pos << "'  IP" << inPct << " List " << cvtToHex(elistp));
            if (!inPct && ch == '%') {
                inPct = true;
                ignore = false;
            } else if (inPct && (std::isdigit(ch) || ch == '.' || ch == '-')) {
            } else if (!inPct) {  // Normal text
            } else {  // Format character
                inPct = false;
                ch = std::tolower(ch);
                switch (ch) {
                case '%': break;
                case '*':
                    inPct = true;  // Get more digits
                    ignore = true;
                    break;
                case 'm': needsScope = true; break;
                case 't':
                    needsTimescale = true;
                    ++formatArgs;
                    break;
                default:
                    if (!ignore && V3Number::displayedFmtHasArg(ch, isScan)) ++formatArgs;
                    break;
                }
            }
        }
    }

    if (vformat.empty() && VN_IS(nodep, Display))  // not fscanf etc, as they need to return value
        return;  // NOP

    const bool isStmt = displayEmitHeader(nodep);

    if (exprFormat) {
        UASSERT_OBJ(exprsp, nodep, "Missing format expression");
        iterateConst(exprsp);
        exprsp = exprsp->nextp();
    } else {
        ofp()->putsQuoted(vformat);
    }

    int exprArgs = 0;
    for (AstNode* argp = exprsp; argp; argp = argp->nextp()) ++exprArgs;
    if (VL_UNCOVERABLE(!exprFormat && exprArgs != formatArgs)) {  // LCOV_EXCL_START
        // expectDisplay() checks this first, so probably internal error if found here
        nodep->v3error("Internal: Missing or extra arguments for $display-like format, "
                       << " expression had " << exprArgs << ", format had " << formatArgs);
    }  // LCOV_EXCL_STOP

    // argc for error check. Also MSVC++ requires va_args to not be off a reference
    int argc = 0;
    if (needsScope) ++argc;
    if (needsTimescale) ++argc;
    for (AstNode* argp = exprsp; argp; argp = argp->nextp()) ++argc;
    ofp()->puts("," + std::to_string(argc));

    if (needsScope) {
        AstScopeName* const scopenamep = fmtp ? fmtp->scopeNamep() : nullptr;
        UASSERT_OBJ(scopenamep, nodep, "Display with %m but no AstScopeName");
        const string suffix = scopenamep->scopePrettySymName();
        ofp()->puts(", '"s + VFormatAttr{VFormatAttr::SCOPE}.ascii() + "'");
        ofp()->puts(",vlSymsp->name(),");
        ofp()->putsQuoted(suffix);
    }

    if (needsTimescale) {
        VTimescale timeunit = VTimescale::NONE;
        if (const AstDisplay* const anodep = VN_CAST(nodep, Display)) {
            timeunit = anodep->fmtp()->timeunit();
        } else if (const AstSFormat* const anodep = VN_CAST(nodep, SFormat)) {
            timeunit = anodep->fmtp()->timeunit();
        } else if (const AstSScanF* const anodep = VN_CAST(nodep, SScanF)) {
            timeunit = anodep->timeunit();
        } else if (const AstSFormatF* const anodep = VN_CAST(nodep, SFormatF)) {
            timeunit = anodep->timeunit();
        }
        UASSERT_OBJ(!timeunit.isNone(), nodep,
                    "Use of %t must be under AstDisplay, AstSFormat, or AstSFormatF, or "
                    "SScanF, and timeunit set");
        ofp()->puts(", '"s + VFormatAttr{VFormatAttr::TIMEUNIT}.ascii() + "'");
        ofp()->puts(","s + cvtToStr((int)timeunit.powerOfTen()));
    }

    // Arguments
    for (AstNode* argp = exprsp; argp; argp = argp->nextp()) {
        ofp()->indentInc();
        ofp()->putbs("");
        AstSFormatArg* const fargp = VN_CAST(argp, SFormatArg);
        AstNode* const subargp = fargp ? fargp->exprp() : argp;
        const VFormatAttr formatAttr = AstSFormatArg::formatAttrDefauled(fargp, subargp->dtypep());
        puts(", '"s + formatAttr.ascii() + '\'');
        if (formatAttr.isSigned() || formatAttr.isUnsigned())
            puts("," + cvtToStr(subargp->widthMin()));
        const bool addrof = isScan || formatAttr.isString() || formatAttr.isComplex();
        puts(",");
        if (addrof) puts("&(");
        iterateConst(subargp);
        if (addrof) puts(")");
        if (!addrof) emitDatap(argp);
        ofp()->indentDec();
    }

    // End
    if (isStmt) {
        puts(");\n");
    } else {
        puts(") ");
    }
}

void EmitCFunc::emitCCallArgs(const AstNodeCCall* nodep, const string& selfPointer,
                              bool inProcess) {
    putns(nodep, "(");
    bool comma = false;
    if (nodep->funcp()->isLoose() && !nodep->funcp()->isStatic()) {
        UASSERT_OBJ(!selfPointer.empty(), nodep, "Call to loose method without self pointer");
        puts(selfPointer);
        comma = true;
    }
    if (nodep->funcp()->needProcess()) {
        if (comma) puts(", ");
        if (VN_IS(nodep->backp(), CAwait) || !nodep->funcp()->isCoroutine()) {
            puts("vlProcess");
        } else if (inProcess) {
            puts("std::make_shared<VlProcess>(vlProcess)");
        } else {
            puts("std::make_shared<VlProcess>()");
        }
        comma = true;
    }
    if (!nodep->argTypes().empty()) {
        if (comma) puts(", ");
        puts(nodep->argTypes());
        comma = true;
    }
    putCommaIterateNext(nodep->argsp(), comma);
    puts(")");
}

std::string EmitCFunc::dereferenceString(const std::string& pointer) const {
    if (pointer[0] == '(' && pointer[1] == '&') {
        // remove "address of" followed by immediate dereference
        // Note: this relies on only the form '(&OBJECT)' being used by Verilator
        return pointer.substr(2, pointer.length() - 3) + '.';
    } else {
        if (pointer == "vlSelf" && m_usevlSelfRef) {
            return "vlSelfRef.";
        } else {
            return pointer + "->";
        }
    }
}
void EmitCFunc::emitDereference(AstNode* nodep, const string& pointer) {
    putns(nodep, dereferenceString(pointer));
}

void EmitCFunc::emitCvtPackStr(AstNode* nodep) {
    if (const AstConst* const constp = VN_CAST(nodep, Const)) {
        emitConstantString(constp);
    } else if (VN_IS(nodep->dtypep(), StreamDType)) {
        putnbs(nodep, "VL_CVT_PACK_STR_ND(");
        iterateAndNextConstNull(nodep);
        puts(")");
    } else {
        putnbs(nodep, "VL_CVT_PACK_STR_N");
        emitIQW(nodep);
        puts("(");
        if (nodep->isWide()) {
            // Note argument width, not node width (which is always 32)
            puts(cvtToStr(nodep->widthWords()));
            puts(", ");
        }
        iterateAndNextConstNull(nodep);
        puts(")");
    }
}

void EmitCFunc::emitCvtWideArray(AstNode* nodep, AstNode* fromp) {
    putnbs(nodep, "VL_CVT_W_A(");
    iterateConst(nodep);
    puts(", ");
    iterateConst(fromp);
    putbs(".atDefault()");  // Not accessed; only to get the proper type of values
    puts(")");
}

void EmitCFunc::emitConstant(AstConst* nodep) {
    // Put out constant set to the specified variable, or given variable in a string
    const V3Number& num = nodep->num();
    if (num.isFourState()) {
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: 4-state numbers in this context");
        return;
    }
    putns(nodep, num.emitC());
}

void EmitCFunc::emitConstantString(const AstConst* nodep) {
    // Const might be a Verilog array-type string, but need to always output std::string
    putnbs(nodep, "std::string{");
    const string str = nodep->num().toString();
    if (!str.empty()) putsQuoted(str);
    puts("}");
}

void EmitCFunc::emitSetVarConstant(const string& assignString, AstConst* constp) {
    puts(assignString);
    puts(" = ");
    emitConstant(constp);
    puts(";\n");
}

void EmitCFunc::emitVarReset(const string& prefix, AstVar* varp, bool constructing) {
    // 'constructing' indicates that the object was just constructed, so if it is a string or
    // something that starts off clear already, no need to clear it again
    AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
    const string vlSelf = VSelfPointerText::replaceThis(m_useSelfForThis, "this->");
    const string varNameProtected
        = ((VN_IS(m_modp, Class) || varp->isFuncLocal()) || !prefix.empty())
              ? varp->nameProtect()
              : vlSelf + varp->nameProtect();
    const string newPrefix = prefix + varNameProtected;
    if (varp->isIO() && m_modp->isTop() && optSystemC()) {
        // System C top I/O doesn't need loading, as the lower level subinst code does it.}
    } else if (varp->isParam()) {
        UASSERT_OBJ(varp->valuep(), varp, "No init for a param?");
        // If a simple CONST value we initialize it using an enum
        // If an ARRAYINIT we initialize it using an initial block similar to a signal
        // puts("// parameter "+varp->nameProtect()+" = "+varp->valuep()->name()+"\n");
    } else if (const AstInitArray* const initarp = VN_CAST(varp->valuep(), InitArray)) {
        // TODO this code probably better handled as initp argument to emitVarResetRecurse
        // TODO merge this functionality with V3EmitCConstInit.h visitors
        if (VN_IS(dtypep, AssocArrayDType)) {
            if (initarp->defaultp()) {
                emitSetVarConstant(newPrefix + ".atDefault()", VN_AS(initarp->defaultp(), Const));
            }
            if (!constructing) puts(varNameProtected + ".clear();");
            const auto& mapr = initarp->map();
            for (const auto& itr : mapr) {
                AstNode* const valuep = itr.second->valuep();
                emitSetVarConstant(newPrefix + ".at(" + cvtToStr(itr.first) + ")",
                                   VN_AS(valuep, Const));
            }
        } else if (VN_IS(dtypep, WildcardArrayDType)) {
            if (initarp->defaultp()) {
                emitSetVarConstant(newPrefix + ".atDefault()", VN_AS(initarp->defaultp(), Const));
            }
            if (!constructing) puts(newPrefix + ".clear();");
            const auto& mapr = initarp->map();
            for (const auto& itr : mapr) {
                AstNode* const valuep = itr.second->valuep();
                emitSetVarConstant(newPrefix + ".at(" + cvtToStr(itr.first) + ")",
                                   VN_AS(valuep, Const));
            }
        } else if (AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            if (initarp->defaultp()) {
                puts("for (int __Vi = 0; __Vi < " + cvtToStr(adtypep->elementsConst()));
                puts("; ++__Vi) {\n");
                emitSetVarConstant(newPrefix + "[__Vi]", VN_AS(initarp->defaultp(), Const));
                puts("}\n");
            }
            const auto& mapr = initarp->map();
            for (const auto& itr : mapr) {
                AstNode* const valuep = itr.second->valuep();
                emitSetVarConstant(newPrefix + "[" + cvtToStr(itr.first) + "]",
                                   VN_AS(valuep, Const));
            }
        } else {
            varp->v3fatalSrc("InitArray under non-arrayed var");
        }
    } else {
        putns(varp,
              emitVarResetRecurse(varp, constructing, newPrefix, dtypep, 0, "", varp->valuep()));
    }
}

string EmitCFunc::emitVarResetRecurse(const AstVar* varp, bool constructing,
                                      const string& varNameProtected, AstNodeDType* dtypep,
                                      int depth, const string& suffix, const AstNode* valuep) {
    dtypep = dtypep->skipRefp();
    AstBasicDType* const basicp = dtypep->basicp();
    // Returns string to do resetting, empty to do nothing (which caller should handle)
    if (AstAssocArrayDType* const adtypep = VN_CAST(dtypep, AssocArrayDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        const string pre = constructing ? "" : varNameProtected + suffix + ".clear();\n";
        return pre
               + emitVarResetRecurse(varp, constructing, varNameProtected, adtypep->subDTypep(),
                                     depth + 1, suffix + ".atDefault()" + cvtarray, nullptr);
    } else if (AstWildcardArrayDType* const adtypep = VN_CAST(dtypep, WildcardArrayDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        const string pre = constructing ? "" : varNameProtected + suffix + ".clear();\n";
        return pre
               + emitVarResetRecurse(varp, constructing, varNameProtected, adtypep->subDTypep(),
                                     depth + 1, suffix + ".atDefault()" + cvtarray, nullptr);
    } else if (VN_IS(dtypep, CDType)) {
        return "";  // Constructor does it
    } else if (VN_IS(dtypep, ClassRefDType)) {
        return "";  // Constructor does it
    } else if (VN_IS(dtypep, IfaceRefDType)) {
        return varNameProtected + suffix + " = nullptr;\n";
    } else if (const AstDynArrayDType* const adtypep = VN_CAST(dtypep, DynArrayDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        const string pre = constructing ? "" : varNameProtected + suffix + ".clear();\n";
        return pre
               + emitVarResetRecurse(varp, constructing, varNameProtected, adtypep->subDTypep(),
                                     depth + 1, suffix + ".atDefault()" + cvtarray, nullptr);
    } else if (const AstQueueDType* const adtypep = VN_CAST(dtypep, QueueDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        const string pre = constructing ? "" : varNameProtected + suffix + ".clear();\n";
        return pre
               + emitVarResetRecurse(varp, constructing, varNameProtected, adtypep->subDTypep(),
                                     depth + 1, suffix + ".atDefault()" + cvtarray, nullptr);
    } else if (VN_IS(dtypep, SampleQueueDType)) {
        return "";
    } else if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
        UASSERT_OBJ(adtypep->hi() >= adtypep->lo(), varp,
                    "Should have swapped msb & lsb earlier.");
        const string ivar = "__Vi"s + cvtToStr(depth);
        const string pre = ("for (int " + ivar + " = " + cvtToStr(0) + "; " + ivar + " < "
                            + cvtToStr(adtypep->elementsConst()) + "; ++" + ivar + ") {\n");
        const string below
            = emitVarResetRecurse(varp, constructing, varNameProtected, adtypep->subDTypep(),
                                  depth + 1, suffix + "[" + ivar + "]", nullptr);
        const string post = "}\n";
        return below.empty() ? "" : pre + below + post;
    } else if (VN_IS(dtypep, NodeUOrStructDType) && !VN_AS(dtypep, NodeUOrStructDType)->packed()) {
        const AstNodeUOrStructDType* const sdtypep = VN_AS(dtypep, NodeUOrStructDType);
        string literal;
        for (const AstMemberDType* itemp = sdtypep->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            const std::string line = emitVarResetRecurse(
                varp, constructing, varNameProtected + suffix + "." + itemp->nameProtect(),
                itemp->dtypep(), depth + 1, "", itemp->valuep());
            if (!line.empty()) literal += line;
        }
        return literal;
    } else if (basicp && basicp->keyword() == VBasicDTypeKwd::STRING) {
        if (constructing) return "";  // String's constructor deals with it
        return varNameProtected + suffix + ".clear();\n";
    } else if (basicp && basicp->isForkSync()) {
        return "";
    } else if (basicp && basicp->isProcessRef()) {
        return "";
    } else if (basicp && basicp->isDelayScheduler()) {
        return "";
    } else if (basicp && basicp->isTriggerScheduler()) {
        return "";
    } else if (basicp && basicp->isDynamicTriggerScheduler()) {
        return "";
    } else if (basicp && (basicp->isRandomGenerator() || basicp->isStdRandomGenerator())) {
        return "";
    } else if (basicp && (basicp->isEvent())) {
        return "VlAssignableEvent{};\n";
    } else if (basicp) {
        const bool zeroit
            = (varp->attrFileDescr()  // Zero so we don't do file IO if never $fopen
               || varp->isFuncLocal()  // Randomization too slow
               || (basicp && basicp->isZeroInit())
               || (v3Global.opt.underlineZero() && !varp->name().empty() && varp->name()[0] == '_')
               || (varp->varType().isTemp() && !varp->isXTemp())
               || (varp->isXTemp()
                       ? (v3Global.opt.xAssign() != "unique")
                       : (v3Global.opt.xInitial() == "fast" || v3Global.opt.xInitial() == "0")));
        const bool slow = !varp->isFuncLocal() && !varp->isClassMember();
        splitSizeInc(1);
        if (dtypep->isWide()) {  // Handle unpacked; not basicp->isWide
            string out;
            if (valuep) {
                const AstConst* const constp = VN_AS(valuep, Const);
                UASSERT_OBJ(constp, varp, "non-const initializer for variable");
                for (int w = 0; w < dtypep->widthWords(); ++w) {
                    out += varNameProtected + suffix + "[" + cvtToStr(w) + "] = ";
                    out += cvtToStr(constp->num().edataWord(w)) + "U;\n";
                }
            } else {
                out += zeroit ? (slow ? "VL_ZERO_RESET_W(" : "VL_ZERO_W(")
                              : (varp->isXTemp() ? "VL_SCOPED_RAND_RESET_ASSIGN_W("
                                                 : "VL_SCOPED_RAND_RESET_W(");
                out += cvtToStr(dtypep->widthMin());
                out += ", " + varNameProtected + suffix;
                if (!zeroit) {
                    emitVarResetScopeHash();
                    const uint64_t salt = VString::hashMurmur(varp->prettyName());
                    out += ", ";
                    out += m_classOrPackage ? m_classOrPackageHash : "__VscopeHash";
                    out += ", ";
                    out += std::to_string(salt);
                    out += "ull";
                }
                out += ");\n";
            }
            return out;
        } else {
            string out = varNameProtected + suffix;
            if (valuep) {
                out += " = ";
                // TODO cleanup code shared between here, V3EmitCConstInit.h,
                // EmitCFunc::emitVarReset, EmitCFunc::emitConstant
                const AstConst* const constp = VN_AS(valuep, Const);
                UASSERT_OBJ(constp, varp, "non-const initializer for variable");
                out += cvtToStr(constp->num().edataWord(0)) + "U;\n";
                out += ";\n";
            } else if (v3Global.opt.fourstate()
                       && (varp->fourstateComplementp() || varp->isFourstateComplement())) {
                V3Number xNum{varp->fileline(), varp->width(), 0};
                bool setTozero = false;
                if (varp->varType() == VVarType::PORT) {
                    const AstNode* iter = varp;
                    while (!iter->firstAbovep()) iter = iter->backp();
                    if (AstModule* const modep = VN_CAST(iter->firstAbovep(), Module)) {
                        setTozero = modep->isTop();
                    }
                }
                if (!setTozero && (varp->isFourstateComplement() || !varp->varType().isNet())) {
                    xNum.setAllBits1();
                }
                out += " = ";
                out += xNum.emitC();
                out += ";\n";
            } else if (zeroit) {
                out += " = 0;\n";
            } else {
                emitVarResetScopeHash();
                const uint64_t salt = VString::hashMurmur(varp->prettyName());
                out += " = VL_SCOPED_RAND_RESET_";
                if (varp->isXTemp()) out += "ASSIGN_";
                out += dtypep->charIQWN();
                out += "(" + cvtToStr(dtypep->widthMin()) + ", "
                       + (m_classOrPackage ? m_classOrPackageHash : "__VscopeHash") + ", "
                       + std::to_string(salt) + "ull);\n";
            }
            return out;
        }
    } else {  // LCOV_EXCL_BR_LINE
        v3fatalSrc("Unknown node type in reset generator: " << varp->prettyTypeName());
    }
    return "";
}

void EmitCFunc::emitVarResetScopeHash() {
    if (VL_LIKELY(m_createdScopeHash)) { return; }
    if (m_classOrPackage) {
        m_classOrPackageHash
            = std::to_string(VString::hashMurmur(m_classOrPackage->name())) + "ULL";
    } else {
        puts(string("const uint64_t __VscopeHash = VL_MURMUR64_HASH(")
             + (m_useSelfForThis ? "vlSelf" : "this") + "->vlNamep);\n");
    }
    m_createdScopeHash = true;
}
