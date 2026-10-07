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
//  constant values of any type, shared across the whole design. Entries are
//  ordinary package variables, deduplicated by value.
//
//*************************************************************************

#ifndef VERILATOR_V3CONSTPOOL_H_
#define VERILATOR_V3CONSTPOOL_H_
#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3HashTable.h"

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
    // Hash and equality of entries in 'm_entries', by value
    struct EntryHash final {
        size_t operator()(const AstVar* varp) const {
            return (*this)(VN_AS(varp->valuep(), NodeExpr));
        }
        size_t operator()(const AstNodeExpr* initp) const { return hashValue(initp).value(); }
    };
    struct EntryEqual final {
        bool operator()(const AstVar* ap, const AstVar* bp) const {  // LCOV_EXCL_START
            return (*this)(ap, VN_AS(bp->valuep(), NodeExpr));  // Only on collision while rebuild
        }  // LCOV_EXCL_STOP
        bool operator()(const AstVar* varp, const AstNodeExpr* initp) const {
            return equalValue(VN_AS(varp->valuep(), NodeExpr), initp);
        }
    };

    // MEMBERS
    Stage m_stage = Stage::UNSCOPED;  // Scoping stage of the design, see setScoped()/setDescoped()
    bool m_cacheValid = false;  // Cache below is up to date
    AstScope* m_scopep = nullptr;  // Scope of the constant pool, between V3Scope and V3Descope
    V3HashSet<AstVar*, EntryHash, EntryEqual> m_entries;  // All entries
    V3HashMap<const AstVar*, AstVarScope*> m_varScopes;  // VarScope of each entry iff m_scopep
    std::array<uint32_t, VNType::NUM_TYPES()> m_nextNumber{};  // Sequence number for naming

    // METHODS
    static V3ConstPool& instance() { return *v3Global.constPoolp(); }
    // Hash of a value, consistent with 'equalValue'
    static V3Hash hashValue(const AstNode* nodep);
    // True if the two values are the same, so can use the same entry
    static bool equalValue(const AstNode* ap, const AstNode* bp);
    // Rebuild the lookup cache from the constant pool package
    void rebuildCache();

    // CONSTRUCTORS - only V3Global creates and deletes the instance
    V3ConstPool() = default;
    ~V3ConstPool() = default;
    VL_UNCOPYABLE(V3ConstPool);
    VL_UNMOVABLE(V3ConstPool);

public:
    // STATIC METHODS
    // Find a constant pool variable with the given constant value, or create one if one does
    // not already exist, and return a read reference to it. The reference has the same dtype
    // as initp. The referenced variable *might* have a different, but compatible dtype.
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
