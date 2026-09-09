// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dfg vertex cache to find existing vertices
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

#include "verilatedos.h"

#include "V3Dfg.h"
#include "V3DfgDataType.h"
#include "V3HashTable.h"

#include <type_traits>

// Type predicate true for cached vertex types
template <typename Vertex>
using V3DfgCacheIsCached
    = std::integral_constant<bool, std::is_base_of<DfgVertexUnary, Vertex>::value
                                       || std::is_base_of<DfgVertexBinary, Vertex>::value
                                       || std::is_base_of<DfgVertexTernary, Vertex>::value>;

// Helper template to determine the cache type for a vertex type
template <typename Vertex, typename CacheBase, typename... Pairs>
struct V3DfgCacheType final {
    using Type = CacheBase;
};

template <typename Vertex, typename CacheBase, typename VertexBase, typename Cache,
          typename... Pairs>
struct V3DfgCacheType<Vertex, CacheBase, VertexBase, Cache, Pairs...> final {
    using Type = std::conditional_t<std::is_base_of<VertexBase, Vertex>::value, Cache,
                                    typename V3DfgCacheType<Vertex, CacheBase, Pairs...>::Type>;
};

class V3DfgCache final {
    // TYPES
    // Hashing and comparison of the cached vertices. Each takes either a vertex, or the
    // parts a vertex would be created from, so a lookup needs no vertex and no key object.

    // DfgSel
    struct HashSel final {
        size_t operator()(const DfgSel* vtxp) const {
            return operator()(vtxp->dtype(), vtxp->fromp(), vtxp->lsb());
        }
        size_t operator()(const DfgDataType& dtype, const DfgVertex* fromp, uint32_t lsb) const {
            // cppcheck-suppress unreadVariable  // cppcheck bug
            V3Hash hash = dtype.hash();
            hash += vertexHash(fromp);
            hash += lsb;
            return hash.value();
        }
    };
    struct EqualSel final {
        bool operator()(const DfgSel* ap, const DfgSel* bp) const {
            return operator()(ap, bp->dtype(), bp->fromp(), bp->lsb());
        }
        bool operator()(const DfgSel* vtxp, const DfgDataType& dtype, const DfgVertex* fromp,
                        uint32_t lsb) const {
            return vtxp->lsb() == lsb && vtxp->dtype() == dtype
                   && vertexEqual(vtxp->fromp(), fromp);
        }
    };

    // DfgVertexUnary
    struct HashUnary final {
        size_t operator()(const DfgVertexUnary* vtxp) const {
            return operator()(vtxp->dtype(), vtxp->inputp(0));
        }
        size_t operator()(const DfgDataType& dtype, const DfgVertex* source0p) const {
            V3Hash hash = dtype.hash();
            hash += vertexHash(source0p);
            return hash.value();
        }
    };
    struct EqualUnary final {
        bool operator()(const DfgVertexUnary* ap, const DfgVertexUnary* bp) const {
            return operator()(ap, bp->dtype(), bp->inputp(0));
        }
        bool operator()(const DfgVertexUnary* vtxp, const DfgDataType& dtype,
                        const DfgVertex* source0p) const {
            return vtxp->dtype() == dtype && vertexEqual(vtxp->inputp(0), source0p);
        }
    };

    // DfgVertexBinary
    struct HashBinary final {
        size_t operator()(const DfgVertexBinary* vtxp) const {
            return operator()(vtxp->dtype(), vtxp->inputp(0), vtxp->inputp(1));
        }
        size_t operator()(const DfgDataType& dtype, const DfgVertex* source0p,
                          const DfgVertex* source1p) const {
            V3Hash hash = dtype.hash();
            hash += vertexHash(source0p);
            hash += vertexHash(source1p);
            return hash.value();
        }
    };
    struct EqualBinary final {
        bool operator()(const DfgVertexBinary* ap, const DfgVertexBinary* bp) const {
            return operator()(ap, bp->dtype(), bp->inputp(0), bp->inputp(1));
        }
        bool operator()(const DfgVertexBinary* vtxp, const DfgDataType& dtype,
                        const DfgVertex* source0p, const DfgVertex* source1p) const {
            return vtxp->dtype() == dtype && vertexEqual(vtxp->inputp(0), source0p)
                   && vertexEqual(vtxp->inputp(1), source1p);
        }
    };

    // DfgVertexTernary
    struct HashTernary final {
        size_t operator()(const DfgVertexTernary* vtxp) const {
            return operator()(vtxp->dtype(), vtxp->inputp(0), vtxp->inputp(1), vtxp->inputp(2));
        }
        size_t operator()(const DfgDataType& dtype, const DfgVertex* source0p,
                          const DfgVertex* source1p, const DfgVertex* source2p) const {
            V3Hash hash = dtype.hash();
            hash += vertexHash(source0p);
            hash += vertexHash(source1p);
            hash += vertexHash(source2p);
            return hash.value();
        }
    };

    struct EqualTernary final {
        bool operator()(const DfgVertexTernary* ap, const DfgVertexTernary* bp) const {
            return operator()(ap, bp->dtype(), bp->inputp(0), bp->inputp(1), bp->inputp(2));
        }
        bool operator()(const DfgVertexTernary* vtxp, const DfgDataType& dtype,
                        const DfgVertex* source0p, const DfgVertex* source1p,
                        const DfgVertex* source2p) const {
            return vtxp->dtype() == dtype && vertexEqual(vtxp->inputp(0), source0p)
                   && vertexEqual(vtxp->inputp(1), source1p)
                   && vertexEqual(vtxp->inputp(2), source2p);
        }
    };

    // Base class of vertex caches
    class CacheBase VL_NOT_FINAL {
    protected:
        // These set the operands of a new vertex
        static void setOperands(DfgSel* vtxp, DfgVertex* fromp, uint32_t lsb) {
            vtxp->fromp(fromp);
            vtxp->lsb(lsb);
        }

        static void setOperands(DfgVertexUnary* vtxp, DfgVertex* src0p) {  //
            vtxp->inputp(0, src0p);
        }

        static void setOperands(DfgVertexBinary* vtxp, DfgVertex* src0p, DfgVertex* src1p) {
            vtxp->inputp(0, src0p);
            vtxp->inputp(1, src1p);
        }

        static void setOperands(DfgVertexTernary* vtxp, DfgVertex* src0p, DfgVertex* src1p,
                                DfgVertex* src2p) {
            vtxp->inputp(0, src0p);
            vtxp->inputp(1, src1p);
            vtxp->inputp(2, src2p);
        }

    public:
        // CacheBase does not cache anything
        virtual DfgVertex* cache(DfgVertex*) { return nullptr; }
        virtual void invalidate(DfgVertex*) {}
    };

    template <typename T_Vertex, typename T_Hash, typename T_Equal>
    class Cache final : public CacheBase {
        static_assert(std::is_base_of<DfgVertex, T_Vertex>::value, "T_Vertex must be a DfgVertex");

        // STATE
        V3HashSet<T_Vertex*, T_Hash, T_Equal> m_set;

    public:
        // Add an existing vertex to the cache. If an equivalent but different vertex exists,
        // it is returned and the cache is not updated. Returns nullptr if the vertex is inserted.
        DfgVertex* cache(DfgVertex* vtxp) override {
            UDEBUGONLY(UASSERT_OBJ(vtxp->is<T_Vertex>(), vtxp, "Vertex is wrong type"););
            T_Vertex* const typedp = static_cast<T_Vertex*>(vtxp);
            T_Vertex* const cachedp = *m_set.insert(typedp).first;
            return cachedp != vtxp ? cachedp : nullptr;
        }
        // Remove an existing vertex from the cache, if it is the cached vertex, otherwise no-op
        void invalidate(DfgVertex* vtxp) override {
            UDEBUGONLY(UASSERT_OBJ(vtxp->is<T_Vertex>(), vtxp, "Vertex is wrong type"););
            T_Vertex* const typedp = static_cast<T_Vertex*>(vtxp);
            const auto it = m_set.find(typedp);
            if (it != m_set.end() && *it == typedp) m_set.erase(it);
        }
        // Get vertex with given operands, return nullptr if not in cache
        template <typename Vertex, typename... Operands>
        Vertex* get(const DfgDataType& dtype, Operands... operands) {
            const auto it = m_set.find(dtype, operands...);
            return it != m_set.end() ? static_cast<Vertex*>(*it) : nullptr;
        }
        // Get vertex with given operands, if does not exist, create it
        template <typename Vertex, typename... Operands>
        Vertex* getOrCreate(DfgGraph& dfg, FileLine* flp, const DfgDataType& dtype,
                            Operands... operands) {
            const auto pair = m_set.insertLazy(dtype, operands..., [&]() -> T_Vertex* {
                Vertex* const newp = new Vertex{dfg, flp, dtype};
                setOperands(newp, operands...);
                return newp;
            });
            T_Vertex* const vtxp = *pair.first;
            UDEBUGONLY(UASSERT_OBJ(vtxp->template is<Vertex>(), vtxp, "Vertex is wrong type"););
            return static_cast<Vertex*>(vtxp);
        }
    };

    // Map from Vertex type to cache type
    // clang-format off
    template <typename Vertex>
    using CacheType = typename V3DfgCacheType<Vertex, CacheBase,
        DfgSel,           /* -> */  Cache<DfgSel, HashSel, EqualSel>,
        DfgVertexUnary,   /* -> */  Cache<DfgVertexUnary, HashUnary, EqualUnary>,
        DfgVertexBinary,  /* -> */  Cache<DfgVertexBinary, HashBinary, EqualBinary>,
        DfgVertexTernary, /* -> */  Cache<DfgVertexTernary, HashTernary, EqualTernary>
    >::Type;
    // clang-format on

    // STATE
    DfgGraph& m_dfg;  // The DfgGraph we are caching the vertices of

// The per type caches
#define VERTEX_CACHE_DECLARE_CACHE(t) CacheType<t> m_cache##t;
    FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE)
#undef VERTEX_CACHE_DECLARE_CACHE

    // Map from vertex type to m_cache* instances for dynamic lookup
    std::array<CacheBase*, VDfgType::NUM_TYPES()> m_vtxType2Cachep{};

    // METHODS

    // Map from vertex type to m_cache* instances for static lookup
    template <typename Vertex>
    CacheType<Vertex>* cacheForType() {
#define VERTEX_CACHE_DECLARE_CACHE(t) \
    if VL_CONSTEXPR_CXX17 (std::is_same<Vertex, t>::value) \
        return reinterpret_cast<CacheType<Vertex>*>(&m_cache##t);
        FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE)
#undef VERTEX_CACHE_DECLARE_CACHE
        return nullptr;  // LCOV_EXCL_LINE
    }

    // Hash constants by value, everything else by identity
    static V3Hash vertexHash(const DfgVertex* vtxp) {
        if (const DfgConst* const constp = vtxp->cast<DfgConst>()) return constp->num().toHash();
        return V3Hash{reinterpret_cast<uint64_t>(vtxp)};
    }

    // Constants are equal by value, everything else is equal by identity
    static bool vertexEqual(const DfgVertex* ap, const DfgVertex* bp) {
        if (ap == bp) return true;
        if (ap->type() != bp->type()) return false;
        if (const DfgConst* const aConstp = ap->cast<DfgConst>()) {
            const DfgConst* const bConstp = bp->as<DfgConst>();
            return aConstp->num().isCaseEq(bConstp->num());
        }
        return false;
    }

public:
    // Note: the cache starts out empty. If the caller wants existing vertices
    // to be found, it must add them itself by calling 'cache' on each.
    explicit V3DfgCache(DfgGraph& dfg)
        : m_dfg{dfg} {
    // Initialize the type to cache lookup table
#define VERTEX_CACHE_DECLARE_CACHE_PTR(t) m_vtxType2Cachep[t::dfgType()] = &m_cache##t;
              FOREACH_DFG_VERTEX_TYPE(VERTEX_CACHE_DECLARE_CACHE_PTR)
#undef VERTEX_CACHE_DECLARE_CACHE_PTR
          }

        // Add an existing vertex to the cache. If an equivalent (but different) already exists,
        // it is returned and the cache is not updated.
        DfgVertex
        * cache(DfgVertex * vtxp) {
        return m_vtxType2Cachep[vtxp->type()]->cache(vtxp);
    }

    // Remove an exiting vertex, it is the cached vertex.
    void invalidate(DfgVertex* vtxp) { m_vtxType2Cachep[vtxp->type()]->invalidate(vtxp); }

    // Find a vertex of type 'Vertex', with the given operands, or create a new one and add it.
    template <typename Vertex, typename... Operands>
    Vertex* getOrCreate(FileLine* flp, const DfgDataType& dtype, Operands... operands) {
        static_assert(std::is_final<Vertex>::value, "Must invoke on final vertex type");
        static_assert(V3DfgCacheIsCached<Vertex>::value, "Not a cached vertex type");
        return cacheForType<Vertex>()->template getOrCreate<Vertex>(m_dfg, flp, dtype,
                                                                    operands...);
    }

    // Find a vertex of type 'Vertex', with the given operands, return nullptr if not in cache.
    template <typename Vertex, typename... Operands>
    Vertex* get(const DfgDataType& dtype, Operands... operands) {
        static_assert(std::is_final<Vertex>::value, "Must invoke on final vertex type");
        static_assert(V3DfgCacheIsCached<Vertex>::value, "Not a cached vertex type");
        return cacheForType<Vertex>()->template get<Vertex>(dtype, operands...);
    }
};

#endif  // VERILATOR_V3DFGCACHE_H_
