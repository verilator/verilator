// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node inline functions
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

#ifndef VERILATOR_V3ASTINLINES_H_
#define VERILATOR_V3ASTINLINES_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h and relaed
#endif

//######################################################################
// Inline METHODS

int AstNode::width() const { return dtypep() ? dtypep()->width() : 0; }
int AstNode::widthMin() const { return dtypep() ? dtypep()->widthMin() : 0; }
bool AstNode::width1() const {  // V3Const uses to know it can optimize
    return dtypep() && dtypep()->width() == 1;
}
int AstNode::widthInstrs() const {
    return (!dtypep() ? 1 : (dtypep()->isWide() ? dtypep()->widthWords() : 1));
}
bool AstNode::isDouble() const VL_MT_SAFE {
    return dtypep() && VN_IS(dtypep(), BasicDType) && VN_AS(dtypep(), BasicDType)->isDouble();
}
bool AstNode::isString() const VL_MT_SAFE {
    return dtypep() && dtypep()->basicp() && dtypep()->basicp()->isString();
}
bool AstNode::isSigned() const { return dtypep() && dtypep()->isSigned(); }

bool AstNode::isZero() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->num().isEqZero());
}
bool AstNode::isNeqZero() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->num().isNeqZero());
}
bool AstNode::isOne() const { return (VN_IS(this, Const) && VN_AS(this, Const)->num().isEqOne()); }
bool AstNode::isAllOnes() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->isEqAllOnes());
}
bool AstNode::isAllOnesV() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->isEqAllOnesV());
}
bool AstNode::sameTree(const AstNode* node2p) const {
    return sameTreeIter(this, node2p, true, false);
}
bool AstNode::sameGateTree(const AstNode* node2p) const {
    return sameTreeIter(this, node2p, true, true);
}

int AstNodeArrayDType::left() const VL_MT_SAFE { return rangep()->leftConst(); }
int AstNodeArrayDType::right() const VL_MT_SAFE { return rangep()->rightConst(); }
int AstNodeArrayDType::hi() const VL_MT_SAFE { return rangep()->hiConst(); }
int AstNodeArrayDType::lo() const VL_MT_SAFE { return rangep()->loConst(); }
int AstNodeArrayDType::elementsConst() const VL_MT_SAFE { return rangep()->elementsConst(); }
VNumRange AstNodeArrayDType::declRange() const VL_MT_SAFE { return VNumRange{left(), right()}; }

AstRange::AstRange(FileLine* fl, int left, int right)
    : ASTGEN_SUPER_Range(fl) {
    leftp(new AstConst{fl, static_cast<uint32_t>(left)});
    rightp(new AstConst{fl, static_cast<uint32_t>(right)});
}
AstRange::AstRange(FileLine* fl, const VNumRange& range)
    : ASTGEN_SUPER_Range(fl) {
    leftp(new AstConst{fl, static_cast<uint32_t>(range.left())});
    rightp(new AstConst{fl, static_cast<uint32_t>(range.right())});
}
int AstRange::leftConst() const {
    AstConst* const constp = VN_CAST(leftp(), Const);
    return (constp ? constp->toSInt() : 0);
}
int AstRange::rightConst() const {
    AstConst* const constp = VN_CAST(rightp(), Const);
    return (constp ? constp->toSInt() : 0);
}

int AstQueueDType::boundConst() const VL_MT_SAFE {
    AstConst* const constp = VN_CAST(boundp(), Const);
    return (constp ? constp->toSInt() : 0);
}

AstPin::AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp)
    : ASTGEN_SUPER_Pin(fl)
    , m_pinNum{pinNum}
    , m_name{varname->name()} {
    this->exprp(exprp);
}

AstPackArrayDType::AstPackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp,
                                     AstRange* rangep)
    : ASTGEN_SUPER_PackArrayDType(fl) {
    childDTypep(dtp);  // Only for parser
    refDTypep(nullptr);
    this->rangep(rangep);
    dtypep(nullptr);  // V3Width will resolve
    const int width = subDTypep()->width() * rangep->elementsConst();
    widthForce(width, width);
}
AstPackArrayDType::AstPackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
    : ASTGEN_SUPER_PackArrayDType(fl) {
    refDTypep(dtp);
    this->rangep(rangep);
    dtypep(this);
    const int width = subDTypep()->width() * rangep->elementsConst();
    widthForce(width, width);
}

int AstBasicDType::hi() const { return (rangep() ? rangep()->hiConst() : m.m_nrange.hi()); }
int AstBasicDType::lo() const { return (rangep() ? rangep()->loConst() : m.m_nrange.lo()); }
int AstBasicDType::elements() const {
    return (rangep() ? rangep()->elementsConst() : m.m_nrange.elements());
}
bool AstBasicDType::littleEndian() const {
    return (rangep() ? rangep()->littleEndian() : m.m_nrange.littleEndian());
}

bool AstActive::hasClocked() const { return m_sensesp->hasClocked(); }
bool AstActive::hasCombo() const { return m_sensesp->hasCombo(); }

AstElabDisplay::AstElabDisplay(FileLine* fl, VDisplayType dispType, AstNode* exprsp)
    : ASTGEN_SUPER_ElabDisplay(fl) {
    addFmtp(new AstSFormatF{fl, AstSFormatF::NoFormat(), exprsp});
    m_displayType = dispType;
}

AstCStmt::AstCStmt(FileLine* fl, const string& textStmt)
    : ASTGEN_SUPER_CStmt(fl) {
    addExprsp(new AstText{fl, textStmt, true});
}

AstCMath::AstCMath(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut)
    : ASTGEN_SUPER_CMath(fl)
    , m_cleanOut{cleanOut}
    , m_pure{true} {
    addExprsp(new AstText{fl, textStmt, true});
    if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
}

AstVarRef::AstVarRef(FileLine* fl, AstVar* varp, const VAccess& access)
    : ASTGEN_SUPER_VarRef(fl, varp->name(), varp, access) {}
// This form only allowed post-link (see above)
AstVarRef::AstVarRef(FileLine* fl, AstVarScope* varscp, const VAccess& access)
    : ASTGEN_SUPER_VarRef(fl, varscp->varp()->name(), varscp->varp(), access) {
    varScopep(varscp);
}
bool AstVarRef::same(const AstVarRef* samep) const {
    if (varScopep()) {
        return (varScopep() == samep->varScopep() && access() == samep->access());
    } else {
        return (selfPointer() == samep->selfPointer() && varp()->name() == samep->varp()->name()
                && access() == samep->access());
    }
}
bool AstVarRef::sameNoLvalue(AstVarRef* samep) const {
    if (varScopep()) {
        return (varScopep() == samep->varScopep());
    } else {
        return (selfPointer() == samep->selfPointer()
                && (!selfPointer().empty() || !samep->selfPointer().empty())
                && varp()->name() == samep->varp()->name());
    }
}

AstVarXRef::AstVarXRef(FileLine* fl, AstVar* varp, const string& dotted, const VAccess& access)
    : ASTGEN_SUPER_VarXRef(fl, varp->name(), varp, access)
    , m_dotted{dotted} {
    dtypeFrom(varp);
}

#endif  // Guard
