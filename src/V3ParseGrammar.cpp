// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse syntax tree
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

#define YYDEBUG 1  // Nicer errors

#include "V3Ast.h"  // This must be before V3ParseBison.cpp, as we don't want #defines to conflict

//======================================================================
// The guts come from bison output

#include "V3ParseBison.c"

//======================================================================
// V3ParseImp functions requiring bison state

int V3ParseImp::bisonParse() {
    // Use --debugi-bison 9 to enable this
    if (PARSEP->debugBison() >= 9) yydebug = 1;
    return yyparse();
}

const char* V3ParseImp::tokenName(int token) {
#if YYDEBUG || YYERROR_VERBOSE
    static const char** nameTablep = nullptr;
    if (!nameTablep) {
        int size;
        for (size = 0; yytname[size]; ++size) {}
        nameTablep = new const char*[size];
        // Workaround bug in bison's which have '!' in yytname but not token values
        int iout = 0;
        for (int i = 0; yytname[i]; ++i) {
            if (yytname[i][0] == '\'') continue;
            nameTablep[iout++] = yytname[i];
        }
    }
    if (token >= 255) {
        return nameTablep[token - 255];
    } else {
        static char ch[2];
        ch[0] = token;
        ch[1] = '\0';
        return ch;
    }
#else
    return "";
#endif
}

void V3ParseImp::parserClear() {
    // Clear up any dynamic memory V3Parser required
    VARDTYPE(nullptr);
}

//======================================================================
// V3ParseGrammar functions requiring bison state

AstArg* V3ParseGrammar::argWrapList(AstNode* nodep) {
    // Convert list of expressions to list of arguments
    if (!nodep) return nullptr;
    AstArg* outp = nullptr;
    AstBegin* const tempp = new AstBegin(nodep->fileline(), "[EditWrapper]", nodep);
    while (nodep) {
        AstNode* const nextp = nodep->nextp();
        AstNode* const exprp = nodep->unlinkFrBack();
        nodep = nextp;
        // addNext can handle nulls:
        outp = AstNode::addNext(outp, new AstArg(exprp->fileline(), "", exprp));
    }
    VL_DO_DANGLING(tempp->deleteTree(), tempp);
    return outp;
}

AstNode* V3ParseGrammar::createSupplyExpr(FileLine* fileline, const string& name, int value) {
    return new AstAssignW(
        fileline, new AstVarRef(fileline, name, VAccess::WRITE),
        new AstConst(fileline, AstConst::StringToParse(), (value ? "'1" : "'0")));
}

AstRange* V3ParseGrammar::scrubRange(AstNodeRange* nrangep) {
    // Remove any UnsizedRange's from list
    for (AstNodeRange *nodep = nrangep, *nextp; nodep; nodep = nextp) {
        nextp = VN_AS(nodep->nextp(), NodeRange);
        if (!VN_IS(nodep, Range)) {
            nodep->v3error(
                "Unsupported or syntax error: Unsized range in instance or other declaration");
            nodep->unlinkFrBack();
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    if (nrangep && nrangep->nextp()) {
        // Not supported by at least 2 of big 3
        nrangep->nextp()->v3warn(E_UNSUPPORTED,
                                 "Unsupported: Multidimensional instances/interfaces.");
        nrangep->nextp()->unlinkFrBackWithNext()->deleteTree();
    }
    return VN_CAST(nrangep, Range);
}

AstNodeDType* V3ParseGrammar::createArray(AstNodeDType* basep, AstNodeRange* nrangep,
                                          bool isPacked) {
    // Split RANGE0-RANGE1-RANGE2
    // into ARRAYDTYPE0(ARRAYDTYPE1(ARRAYDTYPE2(BASICTYPE3), RANGE), RANGE)
    AstNodeDType* arrayp = basep;
    if (nrangep) {  // Maybe no range - return unmodified base type
        while (nrangep->nextp()) nrangep = VN_AS(nrangep->nextp(), NodeRange);
        while (nrangep) {
            AstNodeRange* const prevp = VN_AS(nrangep->backp(), NodeRange);
            if (prevp) nrangep->unlinkFrBack();
            AstRange* const rangep = VN_CAST(nrangep, Range);
            if (rangep && isPacked) {
                arrayp
                    = new AstPackArrayDType(rangep->fileline(), VFlagChildDType(), arrayp, rangep);
            } else if (rangep
                       && (VN_IS(rangep->leftp(), Unbounded)
                           || VN_IS(rangep->rightp(), Unbounded))) {
                arrayp = new AstQueueDType(nrangep->fileline(), VFlagChildDType(), arrayp,
                                           rangep->rightp()->cloneTree(true));
            } else if (rangep) {
                arrayp = new AstUnpackArrayDType(rangep->fileline(), VFlagChildDType(), arrayp,
                                                 rangep);
            } else if (VN_IS(nrangep, UnsizedRange)) {
                arrayp = new AstUnsizedArrayDType(nrangep->fileline(), VFlagChildDType(), arrayp);
            } else if (VN_IS(nrangep, BracketRange)) {
                const AstBracketRange* const arangep = VN_AS(nrangep, BracketRange);
                AstNode* const keyp = arangep->elementsp()->unlinkFrBack();
                arrayp = new AstBracketArrayDType(nrangep->fileline(), VFlagChildDType(), arrayp,
                                                  keyp);
            } else if (VN_IS(nrangep, WildcardRange)) {
                arrayp = new AstWildcardArrayDType{nrangep->fileline(), VFlagChildDType{}, arrayp};
            } else {
                UASSERT_OBJ(0, nrangep, "Expected range or unsized range");
            }
            nrangep = prevp;
        }
    }
    return arrayp;
}

AstVar* V3ParseGrammar::createVariable(FileLine* fileline, const string& name,
                                       AstNodeRange* arrayp, AstNode* attrsp) {
    AstNodeDType* dtypep = GRAMMARP->m_varDTypep;
    UINFO(5, "  creVar " << name << "  decl=" << GRAMMARP->m_varDecl << "  io="
                         << GRAMMARP->m_varIO << "  dt=" << (dtypep ? "set" : "") << endl);
    if (GRAMMARP->m_varIO == VDirection::NONE && GRAMMARP->m_varDecl == VVarType::PORT) {
        // Just a port list with variable name (not v2k format); AstPort already created
        if (dtypep) fileline->v3warn(E_UNSUPPORTED, "Unsupported: Ranges ignored in port-lists");
        return nullptr;
    }
    if (GRAMMARP->m_varDecl == VVarType::WREAL) {
        // dtypep might not be null, might be implicit LOGIC before we knew better
        dtypep = new AstBasicDType(fileline, VBasicDTypeKwd::DOUBLE);
    }
    if (!dtypep) {  // Created implicitly
        dtypep = new AstBasicDType(fileline, LOGIC_IMPLICIT);
    } else {  // May make new variables with same type, so clone
        dtypep = dtypep->cloneTree(false);
    }
    // UINFO(0,"CREVAR "<<fileline->ascii()<<" decl="<<GRAMMARP->m_varDecl.ascii()<<"
    // io="<<GRAMMARP->m_varIO.ascii()<<endl);
    VVarType type = GRAMMARP->m_varDecl;
    if (type == VVarType::UNKNOWN) {
        if (GRAMMARP->m_varIO.isAny()) {
            type = VVarType::PORT;
        } else {
            fileline->v3fatalSrc("Unknown signal type declared: " << type.ascii());
        }
    }
    if (type == VVarType::GENVAR) {
        if (arrayp) fileline->v3error("Genvars may not be arrayed: " << name);
    }

    // Split RANGE0-RANGE1-RANGE2 into
    // ARRAYDTYPE0(ARRAYDTYPE1(ARRAYDTYPE2(BASICTYPE3), RANGE), RANGE)
    AstNodeDType* const arrayDTypep = createArray(dtypep, arrayp, false);

    AstVar* const nodep = new AstVar(fileline, type, name, VFlagChildDType(), arrayDTypep);
    nodep->addAttrsp(attrsp);
    nodep->ansi(m_pinAnsi);
    nodep->declTyped(m_varDeclTyped);
    nodep->lifetime(m_varLifetime);
    nodep->delayp(m_netDelayp);
    m_netDelayp = nullptr;
    if (GRAMMARP->m_varDecl != VVarType::UNKNOWN) nodep->combineType(GRAMMARP->m_varDecl);
    if (GRAMMARP->m_varIO != VDirection::NONE) {
        nodep->declDirection(GRAMMARP->m_varIO);
        nodep->direction(GRAMMARP->m_varIO);
    }

    if (GRAMMARP->m_varDecl == VVarType::SUPPLY0) {
        nodep->addNext(V3ParseGrammar::createSupplyExpr(fileline, nodep->name(), 0));
    }
    if (GRAMMARP->m_varDecl == VVarType::SUPPLY1) {
        nodep->addNext(V3ParseGrammar::createSupplyExpr(fileline, nodep->name(), 1));
    }
    if (VN_IS(dtypep, ParseTypeDType)) {
        // Parser needs to know what is a type
        AstNode* const newp = new AstTypedefFwd(fileline, name);
        nodep->addNext(newp);
        SYMP->reinsert(newp);
    }
    // Don't set dtypep in the ranging;
    // We need to autosize parameters and integers separately
    //
    // Propagate from current module tracing state
    if (nodep->isGenVar()) {
        nodep->trace(false);
    } else if (nodep->isParam() && !v3Global.opt.traceParams()) {
        nodep->trace(false);
    } else {
        nodep->trace(allTracingOn(nodep->fileline()));
    }

    // Remember the last variable created, so we can attach attributes to it in later parsing
    GRAMMARP->m_varAttrp = nodep;
    PARSEP->tagNodep(GRAMMARP->m_varAttrp);
    return nodep;
}

string V3ParseGrammar::deQuote(FileLine* fileline, string text) {
    // Fix up the quoted strings the user put in, for example "\"" becomes "
    // Reverse is V3OutFormatter::quoteNameControls(...)
    bool quoted = false;
    string newtext;
    unsigned char octal_val = 0;
    int octal_digits = 0;
    for (string::const_iterator cp = text.begin(); cp != text.end(); ++cp) {
        if (quoted) {
            if (isdigit(*cp)) {
                octal_val = octal_val * 8 + (*cp - '0');
                if (++octal_digits == 3) {
                    octal_digits = 0;
                    quoted = false;
                    newtext += octal_val;
                }
            } else {
                if (octal_digits) {
                    // Spec allows 1-3 digits
                    octal_digits = 0;
                    quoted = false;
                    newtext += octal_val;
                    --cp;  // Backup to reprocess terminating character as non-escaped
                    continue;
                }
                quoted = false;
                if (*cp == 'n') {
                    newtext += '\n';
                } else if (*cp == 'a') {
                    newtext += '\a';  // SystemVerilog 3.1
                } else if (*cp == 'f') {
                    newtext += '\f';  // SystemVerilog 3.1
                } else if (*cp == 'r') {
                    newtext += '\r';
                } else if (*cp == 't') {
                    newtext += '\t';
                } else if (*cp == 'v') {
                    newtext += '\v';  // SystemVerilog 3.1
                } else if (*cp == 'x' && isxdigit(cp[1])
                           && isxdigit(cp[2])) {  // SystemVerilog 3.1
#define vl_decodexdigit(c) ((isdigit(c) ? ((c) - '0') : (tolower((c)) - 'a' + 10)))
                    newtext
                        += static_cast<char>(16 * vl_decodexdigit(cp[1]) + vl_decodexdigit(cp[2]));
                    cp += 2;
                } else if (isalnum(*cp)) {
                    fileline->v3error("Unknown escape sequence: \\" << *cp);
                    break;
                } else {
                    newtext += *cp;
                }
            }
        } else if (*cp == '\\') {
            quoted = true;
            octal_digits = 0;
        } else if (*cp != '"') {
            newtext += *cp;
        }
    }
    return newtext;
}
