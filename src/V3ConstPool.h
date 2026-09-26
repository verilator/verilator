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
//
//  V3ConstPool finds or creates entries in the constant pool package
//  (AstNetlist::constPoolPkgp()), which holds read-only static data, i.e.:
//  constants, maps and tables, shared across the whole design. Entries are
//  ordinary package variables, deduplicated by value.
//
//*************************************************************************

#ifndef VERILATOR_V3CONSTPOOL_H_
#define VERILATOR_V3CONSTPOOL_H_
#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3HashTable.h"
#include "V3Hasher.h"

//============================================================================

class V3ConstPool final {
    friend class V3Global;  // Owns the instance, needs constructor access

    // TYPES
    // Scoping stage of the design, which determines how entries are referenced
    enum class Stage : uint8_t {
        UNSCOPED,  // Before V3Scope: reference via the package
        SCOPED,  // Between V3Scope and V3Descope: reference via the VarScope
        DESCOPED  // After V3Descope: plain reference
    };
    // Hash and equality of constant entries in 'm_consts'
    struct ConstHash final {
        size_t operator()(const AstVar* varp) const {
            return (*this)(VN_AS(varp->valuep(), Const));
        }
        size_t operator()(const AstConst* initp) const { return initp->num().toHash().value(); }
    };
    struct ConstEqual final {
        bool operator()(const AstVar* ap, const AstVar* bp) const {
            return (*this)(ap, VN_AS(bp->valuep(), Const));
        }
        bool operator()(const AstVar* varp, const AstConst* initp) const {
            // Compare by value, which also checks the width. The dtype is ignored.
            return VN_AS(varp->valuep(), Const)->num().isCaseEq(initp->num());
        }
    };
    // Hash of associative array entries in 'm_maps' and table entries in 'm_tables'
    struct InitArrayHash final {
        size_t operator()(const AstVar* varp) const {
            return (*this)(VN_AS(varp->valuep(), InitArray));
        }
        size_t operator()(const AstInitArray* initp) const {
            return V3Hasher::uncachedHash(initp).value();
        }
    };
    // Equality of associative array entries in 'm_maps'
    struct MapEqual final {
        bool operator()(const AstVar* ap, const AstVar* bp) const {
            return (*this)(ap, VN_AS(bp->valuep(), InitArray));
        }
        bool operator()(const AstVar* varp, const AstInitArray* initp) const {
            return sameMap(VN_AS(varp->valuep(), InitArray), initp);
        }
    };
    // Equality of table entries in 'm_tables'
    struct TableEqual final {
        bool operator()(const AstVar* ap, const AstVar* bp) const {
            return (*this)(ap, VN_AS(bp->valuep(), InitArray));
        }
        bool operator()(const AstVar* varp, const AstInitArray* initp) const {
            return sameTable(VN_AS(varp->valuep(), InitArray), initp);
        }
    };

    // MEMBERS
    Stage m_stage = Stage::UNSCOPED;  // Scoping stage of the design, see setScoped()/setDescoped()
    bool m_cacheValid = false;  // Cache below is up to date
    AstScope* m_scopep = nullptr;  // Scope of the constant pool, between V3Scope and V3Descope
    V3HashSet<AstVar*, ConstHash, ConstEqual> m_consts;  // Packed constants
    V3HashSet<AstVar*, InitArrayHash, MapEqual> m_maps;  // Associative array constants (maps)
    V3HashSet<AstVar*, InitArrayHash, TableEqual> m_tables;  // Unpacked array constants (tables)
    V3HashMap<const AstVar*, AstVarScope*> m_varScopes;  // VarScope of each entry iff m_scopep
    uint32_t m_nextConst = 0;  // Sequence number for naming
    uint32_t m_nextMap = 0;  // Sequence number for naming
    uint32_t m_nextTable = 0;  // Sequence number for naming

    // METHODS
    static V3ConstPool& instance() { return *v3Global.constPoolp(); }
    // Compare associative array or unpacked array initializers by value
    static bool sameMap(const AstInitArray* ap, const AstInitArray* bp);
    static bool sameTable(const AstInitArray* ap, const AstInitArray* bp);
    // Find an entry equal to the given initializer in the given set, or create one named from
    // the given prefix and sequence number, and return a read reference to it
    template <typename T_Set, typename T_Init>
    AstVarRef* findOrCreate(T_Set& set, uint32_t& nextr, const char* prefixp, T_Init* initp);

    // CONSTRUCTORS - only V3Global creates and deletes the instance
    V3ConstPool() = default;
    ~V3ConstPool() = default;
    VL_UNCOPYABLE(V3ConstPool);
    VL_UNMOVABLE(V3ConstPool);

public:
    // STATIC METHODS
    // Find a constant packed variable with the given value, or create one if one does not
    // already exist, and return a read reference to it.
    // The reference has the same dtype as initp.
    // The referenced variable *might* have a different, but compatible dtype.
    static AstVarRef* findConst(AstConst* initp);
    // Find a constant associative array (map) with the given value, or create one if one does
    // not already exist, and return a read reference to it.
    // The reference has the same dtype as initp.
    // The referenced variable *might* have a different, but compatible dtype.
    static AstVarRef* findMap(AstInitArray* initp);
    // Find a constant unpacked array (table) with the given value, or create one if one does
    // not already exist, and return a read reference to it.
    // The reference has the same dtype as initp.
    // The referenced variable *might* have a different, but compatible dtype.
    static AstVarRef* findTable(AstInitArray* initp);
    // Dispatch to the above based on the kind of initializer.
    static AstVarRef* find(AstNodeExpr* initp);
    // Invalidate the lookup cache. This must be called after deleting any Vars from the pool.
    static void invalidateCache() { instance().m_cacheValid = false; }
    // Notify that the design has been scoped, called by V3Scope
    static void setScoped() {
        V3ConstPool& self = instance();
        UASSERT(self.m_stage == Stage::UNSCOPED, "Constant pool scoped twice");
        self.m_stage = Stage::SCOPED;
        invalidateCache();
    }
    // Notify that the design has been descoped, called by V3Descope
    static void setDescoped() {
        V3ConstPool& self = instance();
        UASSERT(self.m_stage == Stage::SCOPED, "Constant pool descoped when not scoped");
        self.m_stage = Stage::DESCOPED;
        invalidateCache();
    }
    // Check the lookup cache refers only to existing nodes, for V3Broken
    static const char* broken();
};

#endif  // Guard
