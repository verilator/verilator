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

#ifndef VERILATOR_V3ASTNODES_H_
#error "Use V3Ast.h as the include"
#include "V3AstNodes.h"  // This helps code analysis tools pick up symbols in V3Ast.h and V3AstNodes.h
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

#endif  // Guard
