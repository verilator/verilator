// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Constant pool
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3ConstPool.h"

//######################################################################
// V3ConstPool

bool V3ConstPool::sameMap(const AstInitArray* ap, const AstInitArray* bp) {
    // Associative array initializers must have equivalent types, defaults, and entries.
    // As in 'sameTable', compare by value, rather than by tree structure.
    const AstAssocArrayDType* const aDTypep = VN_AS(ap->dtypep(), AssocArrayDType);
    const AstAssocArrayDType* const bDTypep = VN_AS(bp->dtypep(), AssocArrayDType);
    if (!aDTypep->subDTypep()->sameTree(bDTypep->subDTypep())) return false;
    if (!aDTypep->keyDTypep()->sameTree(bDTypep->keyDTypep())) return false;
    // The default is optional, but must be the same if present
    const AstNode* const aDefaultp = ap->defaultp();
    const AstNode* const bDefaultp = bp->defaultp();
    UASSERT_OBJ(!aDefaultp || VN_IS(aDefaultp, Const), ap, "Const pool map default not Const");
    UASSERT_OBJ(!bDefaultp || VN_IS(bDefaultp, Const), bp, "Const pool map default not Const");
    if (!aDefaultp != !bDefaultp) return false;
    if (aDefaultp && !aDefaultp->sameTree(bDefaultp)) return false;
    // Compare the entries, which are ordered by key. Note an entry explicitly set to the
    // default value makes maps compare different, which is safe, but misses merging them.
    const AstInitArray::KeyItemMap& aMap = ap->map();
    const AstInitArray::KeyItemMap& bMap = bp->map();
    if (aMap.size() != bMap.size()) return false;
    auto bIt = bMap.cbegin();
    for (const auto& aItem : aMap) {
        const AstNode* const aValuep = aItem.second->valuep();
        const AstNode* const bValuep = bIt->second->valuep();
        UASSERT_OBJ(VN_IS(aValuep, Const), aValuep, "Const pool map item not Const");
        UASSERT_OBJ(VN_IS(bValuep, Const), bValuep, "Const pool map item not Const");
        if (aItem.first != bIt->first) return false;
        if (!aValuep->sameTree(bValuep)) return false;
        ++bIt;
    }
    return true;
}

bool V3ConstPool::sameTable(const AstInitArray* ap, const AstInitArray* bp) {
    // Unpacked array initializers must have equivalent values
    // Note, sadly we can't just call ap->sameTree(pb), because both:
    // - the dtypes might be different instances
    // - the default/inititem children might be in different order yet still yield the same table
    // See note in AstInitArray::same about the same. This function instead compares by initializer
    // value, rather than by tree structure.
    const AstUnpackArrayDType* const aDTypep = VN_AS(ap->dtypep(), UnpackArrayDType);
    const AstUnpackArrayDType* const bDTypep = VN_AS(bp->dtypep(), UnpackArrayDType);
    if (!aDTypep->subDTypep()->sameTree(bDTypep->subDTypep())) return false;
    if (!aDTypep->rangep()->sameTree(bDTypep->rangep())) return false;
    // Compare initializer arrays by value. Note this is only called when they hash the same.
    const uint64_t size = aDTypep->elementsConst();
    for (uint64_t n = 0; n < size; ++n) {
        const AstNode* const valAp = ap->getIndexDefaultedValuep(n);
        const AstNode* const valBp = bp->getIndexDefaultedValuep(n);
        UASSERT_OBJ(VN_IS(valAp, Const), valAp, "Const pool table item not Const");
        UASSERT_OBJ(VN_IS(valBp, Const), valBp, "Const pool table item not Const");
        if (!valAp->sameTree(valBp)) return false;
    }
    return true;
}

template <typename T_Set, typename T_Init>
AstVarRef* V3ConstPool::findOrCreate(T_Set& set, uint32_t& nextr, const char* prefixp,
                                     T_Init* initp) {
    // Rebuild the cache if invalidated
    if (VL_UNLIKELY(!m_cacheValid)) {
        m_cacheValid = true;
        m_scopep = nullptr;
        m_consts.clear();
        m_maps.clear();
        m_tables.clear();
        m_varScopes.clear();
        AstPackage* const pkgp = v3Global.rootp()->constPoolPkgp();
        for (AstNode* nodep = pkgp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstScope* const scopep = VN_CAST(nodep, Scope)) {
                if (m_stage == Stage::SCOPED) m_scopep = scopep;
                continue;
            }
            // Otherwise must be a variable
            AstVar* const varp = VN_AS(nodep, Var);
            UASSERT_OBJ(varp->constPoolEntry(), varp, "Unmarked variable in constant pool");
            if (VN_IS(varp->valuep(), Const)) {
                m_consts.insert(varp);
            } else if (const AstInitArray* const arrayp = VN_CAST(varp->valuep(), InitArray)) {
                if (VN_IS(arrayp->dtypep(), AssocArrayDType)) {
                    m_maps.insert(varp);
                } else {
                    m_tables.insert(varp);
                }
            }
        }
        if (m_scopep) {
            for (AstVarScope* vscp = m_scopep->varsp(); vscp;
                 vscp = VN_AS(vscp->nextp(), VarScope)) {
                m_varScopes.insert({vscp->varp(), vscp});
            }
        }
    }

    FileLine* const flp = initp->fileline();
    AstNodeDType* const dtypep = initp->dtypep();

    // Look up/create the variable with this value
    const auto pair = set.insertLazy(initp, [&]() {
        const std::string name = prefixp + std::to_string(nextr++);
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};
        varp->setConstPoolEntry();
        varp->lifetime(VLifetime::STATIC_EXPLICIT);
        varp->isConst(true);
        varp->isStatic(true);
        varp->valuep(initp->cloneTree(false));
        v3Global.rootp()->constPoolPkgp()->addStmtsp(varp);
        return varp;
    });
    AstVar* const varp = *pair.first;

    // Create a read reference to the entry, of the right form for the current stage
    AstVarRef* refp = nullptr;
    switch (m_stage) {
    case Stage::UNSCOPED: {
        // Before V3Scope, reference via the package, as any other package variable
        AstPackage* const pkgp = v3Global.rootp()->constPoolPkgp();
        refp = new AstVarRef{flp, pkgp, varp, VAccess::READ};
        break;
    }
    case Stage::SCOPED: {
        // While scoped, reference the VarScope, creating it for a new entry, or if removed
        const auto vscpPair = m_varScopes.insertLazy(varp, [&]() {
            AstVarScope* const vscp = new AstVarScope{varp->fileline(), m_scopep, varp};
            m_scopep->addVarsp(vscp);
            return std::pair<const AstVar*, AstVarScope*>{varp, vscp};
        });
        refp = new AstVarRef{flp, vscpPair.first->second, VAccess::READ};
        break;
    }
    case Stage::DESCOPED: {
        // After V3Descope, no VarScope is needed
        refp = new AstVarRef{flp, varp, VAccess::READ};
        break;
    }
    }

    // The entry might have been created with a different, but compatible dtype
    refp->dtypep(dtypep);
    return refp;
}

AstVarRef* V3ConstPool::findConst(AstConst* initp) {
    V3ConstPool& self = instance();
    return self.findOrCreate(self.m_consts, self.m_nextConst, "CONST_", initp);
}

AstVarRef* V3ConstPool::findMap(AstInitArray* initp) {
    UASSERT_OBJ(VN_IS(initp->dtypep(), AssocArrayDType), initp,
                "Const pool map must have associative array dtype");
    V3ConstPool& self = instance();
    return self.findOrCreate(self.m_maps, self.m_nextMap, "MAP_", initp);
}

AstVarRef* V3ConstPool::findTable(AstInitArray* initp) {
    UASSERT_OBJ(VN_IS(initp->dtypep(), UnpackArrayDType), initp,
                "Const pool table must have unpacked array dtype");
    V3ConstPool& self = instance();
    return self.findOrCreate(self.m_tables, self.m_nextTable, "TABLE_", initp);
}

AstVarRef* V3ConstPool::find(AstNodeExpr* initp) {
    if (AstConst* const constp = VN_CAST(initp, Const)) return findConst(constp);
    if (AstInitArray* const arrayp = VN_CAST(initp, InitArray)) {
        if (VN_IS(arrayp->dtypep(), AssocArrayDType)) return findMap(arrayp);
        if (VN_IS(arrayp->dtypep(), UnpackArrayDType)) return findTable(arrayp);
    }
    initp->v3fatalSrc("Unhandled constant pool initializer");
    return nullptr;  // LCOV_EXCL_LINE
}

const char* V3ConstPool::broken() {
    const V3ConstPool& self = instance();
    if (!self.m_cacheValid) return nullptr;
    BROKEN_RTN(self.m_scopep && !self.m_scopep->brokeExists());
    for (const AstVar* const varp : self.m_consts) BROKEN_RTN(!varp->brokeExists());
    for (const AstVar* const varp : self.m_maps) BROKEN_RTN(!varp->brokeExists());
    for (const AstVar* const varp : self.m_tables) BROKEN_RTN(!varp->brokeExists());
    for (const auto& pair : self.m_varScopes) {
        BROKEN_RTN(!pair.first->brokeExists());
        BROKEN_RTN(!pair.second->brokeExists());
    }
    return nullptr;
}
