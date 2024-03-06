// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dfg vertex cache to find existing vertices
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// A cache for DfgGraph, to find existing vertices with identical inputs.
//
// Beware that if you use this data-structure, you must invalidate the
// cache any time you change the inputs of an existing vertex, otherwise
// you will have a very bad day.
//
//*************************************************************************

#ifndef VERILATOR_V3DFGCACHE_H_
#define VERILATOR_V3DFGCACHE_H_

#include "V3Dfg.h"

#include <tuple>

// Template specializatoins must be defiend before they are used,
// so this is implemented in a namespace

namespace V3DfgCacheInternal {

// Hash constants by value, everything else by identity
inline V3Hash vertexHash(const DfgVertex* vtxp) {
    if (const DfgConst* const constp = vtxp->cast<DfgConst>()) return constp->num().toHash();
    return V3Hash{reinterpret_cast<uint64_t>(vtxp)};
}

// Constants are equal by value, everything else is equal by identity
inline bool vertexEqual(const DfgVertex* ap, const DfgVertex* bp) {
    if (ap == bp) return true;
    if (ap->type() != bp->type()) return false;
    if (const DfgConst* const aConstp = ap->cast<DfgConst>()) {
        const DfgConst* const bConstp = bp->as<DfgConst>();
        return aConstp->num().isCaseEq(bConstp->num());
    }
    return false;
}

class KeySel final {
    const DfgVertex* const m_fromp;
    const uint32_t m_lsb;
    const uint32_t m_width;

public:
    KeySel(DfgVertex* fromp, uint32_t lsb, uint32_t width)
        : m_fromp{fromp}
        , m_lsb{lsb}
        , m_width{width} {}

    struct Hash final {
        size_t operator()(const KeySel& key) const {
            V3Hash hash{vertexHash(key.m_fromp)};
            hash += key.m_lsb;
            hash += key.m_width;
            return hash.value();
        }
    };

    struct Equal final {
        bool operator()(const KeySel& a, const KeySel& b) const {
            return a.m_lsb == b.m_lsb && a.m_width == b.m_width
                   && vertexEqual(a.m_fromp, b.m_fromp);
        }
    };
};

class KeyUnary final {
    const DfgVertex* const m_source0p;

public:
    KeyUnary(DfgVertex* source0p)
        : m_source0p{source0p} {}

    struct Hash final {
        size_t operator()(const KeyUnary& key) const {  //
            return vertexHash(key.m_source0p).value();
        }
    };

    struct Equal final {
        bool operator()(const KeyUnary& a, const KeyUnary& b) const {
            return vertexEqual(a.m_source0p, b.m_source0p);
        }
    };
};

class KeyBinary final {
    const DfgVertex* const m_source0p;
    const DfgVertex* const m_source1p;

public:
    KeyBinary(DfgVertex* source0p, DfgVertex* source1p)
        : m_source0p{source0p}
        , m_source1p{source1p} {}

    struct Hash final {
        size_t operator()(const KeyBinary& key) const {
            V3Hash hash{vertexHash(key.m_source0p)};
            hash += vertexHash(key.m_source1p);
            return hash.value();
        }
    };

    struct Equal final {
        bool operator()(const KeyBinary& a, const KeyBinary& b) const {
            return vertexEqual(a.m_source0p, b.m_source0p)
                   && vertexEqual(a.m_source1p, b.m_source1p);
        }
    };
};

class KeyTernary final {
    const DfgVertex* const m_source0p;
    const DfgVertex* const m_source1p;
    const DfgVertex* const m_source2p;

public:
    KeyTernary(DfgVertex* source0p, DfgVertex* source1p, DfgVertex* source2p)
        : m_source0p{source0p}
        , m_source1p{source1p}
        , m_source2p{source2p} {}

    struct Hash final {
        size_t operator()(const KeyTernary& key) const {
            V3Hash hash{vertexHash(key.m_source0p)};
            hash += vertexHash(key.m_source1p);
            hash += vertexHash(key.m_source2p);
            return hash.value();
        }
    };

    struct Equal final {
        bool operator()(const KeyTernary& a, const KeyTernary& b) const {
            return vertexEqual(a.m_source0p, b.m_source0p)
                   && vertexEqual(a.m_source1p, b.m_source1p)
                   && vertexEqual(a.m_source2p, b.m_source2p);
        }
    };
};

template <typename Key, typename Val>
using Cache = std::unordered_map<Key, Val, typename Key::Hash, typename Key::Equal>;

using CacheSel = Cache<KeySel, DfgSel*>;
using CacheUnary = Cache<KeyUnary, DfgVertexUnary*>;
using CacheBinary = Cache<KeyBinary, DfgVertexBinary*>;
using CacheTernary = Cache<KeyTernary, DfgVertexTernary*>;

// These return a reference to the mapped entry, inserting a nullptr if not yet exists
inline DfgSel*& getEntry(CacheSel& cache, AstNodeDType* dtypep, DfgVertex* src0p, uint32_t lsb) {
    UASSERT_OBJ(VN_IS(dtypep, BasicDType), dtypep, "non-packed has no 'width()'");
    return cache
        .emplace(std::piecewise_construct,  //
                 std::forward_as_tuple(src0p, lsb, dtypep->width()),  //
                 std::forward_as_tuple(nullptr))
        .first->second;
}

inline DfgVertexUnary*& getEntry(CacheUnary& cache, AstNodeDType*, DfgVertex* src0p) {
    return cache
        .emplace(std::piecewise_construct,  //
                 std::forward_as_tuple(src0p),  //
                 std::forward_as_tuple(nullptr))
        .first->second;
}

inline DfgVertexBinary*& getEntry(CacheBinary& cache, AstNodeDType*, DfgVertex* src0p,
                                  DfgVertex* src1p) {
    return cache
        .emplace(std::piecewise_construct,  //
                 std::forward_as_tuple(src0p, src1p),  //
                 std::forward_as_tuple(nullptr))
        .first->second;
}

inline DfgVertexTernary*& getEntry(CacheTernary& cache, AstNodeDType*, DfgVertex* src0p,
                                   DfgVertex* src1p, DfgVertex* src2p) {
    return cache
        .emplace(std::piecewise_construct,  //
                 std::forward_as_tuple(src0p, src1p, src2p),  //
                 std::forward_as_tuple(nullptr))
        .first->second;
}

// These return a reference to the mapped entry, inserting a nullptr if not yet exists
inline CacheSel::iterator find(CacheSel& cache, AstNodeDType* dtypep, DfgVertex* src0p,
                               uint32_t lsb) {
    UASSERT_OBJ(VN_IS(dtypep, BasicDType), dtypep, "non-packed has no 'width()'");
    const uint32_t width = dtypep->width();
    return cache.find({src0p, lsb, width});
}

inline CacheUnary::iterator find(CacheUnary& cache, AstNodeDType*, DfgVertex* src0p) {
    return cache.find({src0p});
}

inline CacheBinary::iterator find(CacheBinary& cache, AstNodeDType*, DfgVertex* src0p,
                                  DfgVertex* src1p) {
    return cache.find({src0p, src1p});
}

inline CacheTernary::iterator find(CacheTernary& cache, AstNodeDType*, DfgVertex* src0p,
                                   DfgVertex* src1p, DfgVertex* src2p) {
    return cache.find({src0p, src1p, src2p});
}

// These set the operands of a new vertex
inline void setOperands(DfgSel* vtxp, DfgVertex* fromp, uint32_t lsb) {
    vtxp->fromp(fromp);
    vtxp->lsb(lsb);
}

inline void setOperands(DfgVertexUnary* vtxp, DfgVertex* src0p) {  //
    vtxp->relinkSource<0>(src0p);
}

inline void setOperands(DfgVertexBinary* vtxp, DfgVertex* src0p, DfgVertex* src1p) {
    vtxp->relinkSource<0>(src0p);
    vtxp->relinkSource<1>(src1p);
}

inline void setOperands(DfgVertexTernary* vtxp, DfgVertex* src0p, DfgVertex* src1p,
                        DfgVertex* src2p) {
    vtxp->relinkSource<0>(src0p);
    vtxp->relinkSource<1>(src1p);
    vtxp->relinkSource<2>(src2p);
}

// Get or create (and insert) vertex with given operands
template <typename Vertex, typename Cache, typename... Operands>
inline Vertex* getOrCreate(DfgGraph& dfg, FileLine* flp, AstNodeDType* dtypep, Cache& cache,
                           Operands... operands) {
    typename Cache::mapped_type& entrypr = getEntry(cache, dtypep, operands...);
    if (!entrypr) {
        Vertex* const newp = new Vertex{dfg, flp, dtypep};
        setOperands(newp, operands...);
        entrypr = newp;
    }
    return reinterpret_cast<Vertex*>(entrypr);
}

// These add an existing vertex to the table, if an equivalent does not yet exist
inline void cache(CacheSel& cache, DfgSel* vtxp) {
    DfgSel*& entrypr = getEntry(cache, vtxp->dtypep(), vtxp->fromp(), vtxp->lsb());
    if (!entrypr) entrypr = vtxp;
}

inline void cache(CacheUnary& cache, DfgVertexUnary* vtxp) {
    DfgVertexUnary*& entrypr = getEntry(cache, vtxp->dtypep(), vtxp->source<0>());
    if (!entrypr) entrypr = vtxp;
}

inline void cache(CacheBinary& cache, DfgVertexBinary* vtxp) {
    DfgVertexBinary*& entrypr
        = getEntry(cache, vtxp->dtypep(), vtxp->source<0>(), vtxp->source<1>());
    if (!entrypr) entrypr = vtxp;
}

inline void cache(CacheTernary& cache, DfgVertexTernary* vtxp) {
    DfgVertexTernary*& entrypr
        = getEntry(cache, vtxp->dtypep(), vtxp->source<0>(), vtxp->source<1>(), vtxp->source<2>());
    if (!entrypr) entrypr = vtxp;
}

// These remove an existing vertex from the cache, if it is the cached vertex
inline void invalidateByValue(CacheSel& cache, DfgSel* vtxp) {
    const auto it = find(cache, vtxp->dtypep(), vtxp->fromp(), vtxp->lsb());
    if (it != cache.end() && it->second == vtxp) cache.erase(it);
}

inline void invalidateByValue(CacheUnary& cache, DfgVertexUnary* vtxp) {
    const auto it = find(cache, vtxp->dtypep(), vtxp->source<0>());
    if (it != cache.end() && it->second == vtxp) cache.erase(it);
}

inline void invalidateByValue(CacheBinary& cache, DfgVertexBinary* vtxp) {
    const auto it = find(cache, vtxp->dtypep(), vtxp->source<0>(), vtxp->source<1>());
    if (it != cache.end() && it->second == vtxp) cache.erase(it);
}

inline void invalidateByValue(CacheTernary& cache, DfgVertexTernary* vtxp) {
    const auto it
        = find(cache, vtxp->dtypep(), vtxp->source<0>(), vtxp->source<1>(), vtxp->source<2>());
    if (it != cache.end() && it->second == vtxp) cache.erase(it);
}

// clang-format off

// This type defines the cache type corresponding to a vertex type
template <typename Vertex> struct CacheTypeImpl : public CacheTypeImpl<typename Vertex::Super> {};
template <> struct CacheTypeImpl<DfgSel> { using type = CacheSel; };
template <> struct CacheTypeImpl<DfgVertexUnary> { using type = CacheUnary; };
template <> struct CacheTypeImpl<DfgVertexBinary> { using type = CacheBinary; };
template <> struct CacheTypeImpl<DfgVertexTernary> { using type = CacheTernary; };
template <typename Vertex> using CacheType = typename CacheTypeImpl<Vertex>::type;

// Just add new lines in here for new vertex types you need to be able to cache

#define FOREACH_CACHED_VERTEX_TYPE(macro) \
    macro(DfgSel) \
    macro(DfgNot) \
    macro(DfgNegate) \
    macro(DfgConcat) \
    macro(DfgNeq) \
    macro(DfgShiftL) \
    macro(DfgShiftR) \
    macro(DfgShiftRS) \
    macro(DfgAdd) \
    macro(DfgSub) \
    macro(DfgMul) \
    macro(DfgMulS) \
    macro(DfgEq) \
    macro(DfgAnd) \
    macro(DfgOr) \
    macro(DfgXor) \
    macro(DfgRedAnd) \
    macro(DfgRedOr) \
    macro(DfgRedXor) \
    macro(DfgCond)

// clang-format on

class V3DfgCache final {
    DfgGraph& m_dfg;  // The DfgGraph we are caching the vertices of

    // The per type caches
#define VERTEX_CACHE_DECLARE_LUT(t) CacheType<t> m_cache##t;
    FOREACH_CACHED_VERTEX_TYPE(VERTEX_CACHE_DECLARE_LUT)
#undef VERTEX_CACHE_DECLARE_LUT

    // Specializations return one of the above m_cache members
    template <typename Vertex>
    inline CacheType<Vertex>& cacheForType();

public:
    V3DfgCache(DfgGraph& dfg)
        : m_dfg{dfg} {}

    // Find a vertex of type 'Vertex', with the given operands, or create a new one and add it.
    template <typename Vertex, typename... Operands>
    inline Vertex* getOrCreate(FileLine* flp, AstNodeDType* dtypep, Operands... operands);

    // Add an existing vertex of the table. If an equivalent already exists, then nothing happens.
    void cache(DfgVertex* vtxp);

    // Remove an exiting vertex, it is the cached vertex.
    void invalidateByValue(DfgVertex* vtxp);
};

// clang-format off
// The per-type specializations of 'V3DfgCache::cacheForType'
#define VERTEX_CACHE_DEFINE_LUT_SPECIALIZATION(t) \
    template <> inline CacheType<t>& V3DfgCache::cacheForType<t>() {  return m_cache ## t; }
FOREACH_CACHED_VERTEX_TYPE(VERTEX_CACHE_DEFINE_LUT_SPECIALIZATION)
#undef VERTEX_CACHE_DEFINE_LUT_SPECIALIZATION
// clang-format on

// Find a vertex of type 'Vertex', with the given operands, or create a new one and add it
template <typename Vertex, typename... Operands>
Vertex* V3DfgCache::getOrCreate(FileLine* flp, AstNodeDType* dtypep, Operands... operands) {
    static_assert(std::is_final<Vertex>::value, "Must invoke on final vertex type");
    constexpr bool isSel = std::is_same<DfgSel, Vertex>::value;
    constexpr bool isUnary = !isSel && std::is_base_of<DfgVertexUnary, Vertex>::value;
    constexpr bool isBinary = std::is_base_of<DfgVertexBinary, Vertex>::value;
    constexpr bool isTernary = std::is_base_of<DfgVertexTernary, Vertex>::value;
    static_assert(isSel || isUnary || isBinary || isTernary,
                  "'get' called with unknown vertex type");

    static_assert(!isSel || sizeof...(Operands) == 2,  //
                  "Wrong number of operands to DfgSel");
    static_assert(!isUnary || sizeof...(Operands) == 1,
                  "Wrong number of operands to unary vertex");
    static_assert(!isBinary || sizeof...(Operands) == 2,
                  "Wrong number of operands to binary vertex");
    static_assert(!isTernary || sizeof...(Operands) == 3,
                  "Wrong number of operands to ternary vertex");

    return V3DfgCacheInternal::getOrCreate<Vertex, CacheType<Vertex>, Operands...>(
        m_dfg, flp, dtypep, cacheForType<Vertex>(), operands...);
}

}  // namespace V3DfgCacheInternal

// Export only the public interface class
using V3DfgCacheInternal::V3DfgCache;

#endif  // VERILATOR_V3DFGCACHE_H_
