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

inline AstNode* AstNode::addNext(AstNode* newp) { return addNext(this, newp); }
inline AstNode* AstNode::addNextNull(AstNode* newp) { return addNextNull(this, newp); }
inline void AstNode::addPrev(AstNode* newp) {
    replaceWith(newp);
    newp->addNext(this);
}

inline int AstNode::width() const { return dtypep() ? dtypep()->width() : 0; }
inline int AstNode::widthMin() const { return dtypep() ? dtypep()->widthMin() : 0; }
inline bool AstNode::width1() const {  // V3Const uses to know it can optimize
    return dtypep() && dtypep()->width() == 1;
}
inline int AstNode::widthInstrs() const {
    return (!dtypep() ? 1 : (dtypep()->isWide() ? dtypep()->widthWords() : 1));
}
inline bool AstNode::isDouble() const {
    return dtypep() && VN_IS(dtypep(), BasicDType) && VN_AS(dtypep(), BasicDType)->isDouble();
}
inline bool AstNode::isString() const {
    return dtypep() && dtypep()->basicp() && dtypep()->basicp()->isString();
}
inline bool AstNode::isSigned() const { return dtypep() && dtypep()->isSigned(); }

inline bool AstNode::isZero() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->num().isEqZero());
}
inline bool AstNode::isNeqZero() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->num().isNeqZero());
}
inline bool AstNode::isOne() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->num().isEqOne());
}
inline bool AstNode::isAllOnes() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->isEqAllOnes());
}
inline bool AstNode::isAllOnesV() const {
    return (VN_IS(this, Const) && VN_AS(this, Const)->isEqAllOnesV());
}
inline bool AstNode::sameTree(const AstNode* node2p) const {
    return sameTreeIter(this, node2p, true, false);
}
inline bool AstNode::sameGateTree(const AstNode* node2p) const {
    return sameTreeIter(this, node2p, true, true);
}

inline void AstNodeVarRef::varp(AstVar* varp) {
    m_varp = varp;
    dtypeFrom(varp);
}

inline bool AstNodeDType::isFourstate() const { return basicp()->isFourstate(); }

inline void AstNodeArrayDType::rangep(AstRange* nodep) { setOp2p(nodep); }
inline int AstNodeArrayDType::left() const { return rangep()->leftConst(); }
inline int AstNodeArrayDType::right() const { return rangep()->rightConst(); }
inline int AstNodeArrayDType::hi() const { return rangep()->hiConst(); }
inline int AstNodeArrayDType::lo() const { return rangep()->loConst(); }
inline int AstNodeArrayDType::elementsConst() const { return rangep()->elementsConst(); }
inline VNumRange AstNodeArrayDType::declRange() const { return VNumRange{left(), right()}; }

inline void AstIfaceRefDType::cloneRelink() {
    if (m_cellp && m_cellp->clonep()) m_cellp = m_cellp->clonep();
    if (m_ifacep && m_ifacep->clonep()) m_ifacep = m_ifacep->clonep();
    if (m_modportp && m_modportp->clonep()) m_modportp = m_modportp->clonep();
}

AstRange::AstRange(FileLine* fl, int left, int right)
    : ASTGEN_SUPER_Range(fl) {
    setOp2p(new AstConst{fl, static_cast<uint32_t>(left)});
    setOp3p(new AstConst{fl, static_cast<uint32_t>(right)});
}
AstRange::AstRange(FileLine* fl, const VNumRange& range)
    : ASTGEN_SUPER_Range(fl) {
    setOp2p(new AstConst{fl, static_cast<uint32_t>(range.left())});
    setOp3p(new AstConst{fl, static_cast<uint32_t>(range.right())});
}
int AstRange::leftConst() const {
    AstConst* const constp = VN_CAST(leftp(), Const);
    return (constp ? constp->toSInt() : 0);
}
int AstRange::rightConst() const {
    AstConst* const constp = VN_CAST(rightp(), Const);
    return (constp ? constp->toSInt() : 0);
}

int AstQueueDType::boundConst() const {
    AstConst* const constp = VN_CAST(boundp(), Const);
    return (constp ? constp->toSInt() : 0);
}

AstPin::AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp)
    : ASTGEN_SUPER_Pin(fl)
    , m_pinNum{pinNum}
    , m_name{varname->name()} {
    setNOp1p(exprp);
}

AstDpiExportUpdated::AstDpiExportUpdated(FileLine* fl, AstVarScope* varScopep)
    : ASTGEN_SUPER_DpiExportUpdated(fl) {
    addOp1p(new AstVarRef{fl, varScopep, VAccess::WRITE});
}

AstVarScope* AstDpiExportUpdated::varScopep() const { return VN_AS(op1p(), VarRef)->varScopep(); }

AstPackArrayDType::AstPackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp,
                                     AstRange* rangep)
    : ASTGEN_SUPER_PackArrayDType(fl) {
    childDTypep(dtp);  // Only for parser
    refDTypep(nullptr);
    setOp2p(rangep);
    dtypep(nullptr);  // V3Width will resolve
    const int width = subDTypep()->width() * rangep->elementsConst();
    widthForce(width, width);
}
AstPackArrayDType::AstPackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
    : ASTGEN_SUPER_PackArrayDType(fl) {
    refDTypep(dtp);
    setOp2p(rangep);
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

bool AstActive::hasInitial() const { return m_sensesp->hasInitial(); }
bool AstActive::hasSettle() const { return m_sensesp->hasSettle(); }
bool AstActive::hasClocked() const { return m_sensesp->hasClocked(); }

AstElabDisplay::AstElabDisplay(FileLine* fl, VDisplayType dispType, AstNode* exprsp)
    : ASTGEN_SUPER_ElabDisplay(fl) {
    setOp1p(new AstSFormatF{fl, AstSFormatF::NoFormat(), exprsp});
    m_displayType = dispType;
}

AstCStmt::AstCStmt(FileLine* fl, const string& textStmt)
    : ASTGEN_SUPER_CStmt(fl) {
    addNOp1p(new AstText{fl, textStmt, true});
}

AstCMath::AstCMath(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut)
    : ASTGEN_SUPER_CMath(fl)
    , m_cleanOut{cleanOut}
    , m_pure{true} {
    addNOp1p(new AstText{fl, textStmt, true});
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
