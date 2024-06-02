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
// Beware that if you use data-structure, you must invalidate the cache any
// time you change the inputs of an existing vertex, otherwise you will
// have a very bad day.
//
//*************************************************************************

#include "V3DfgCache.h"

namespace V3DfgCacheInternal {

void V3DfgCache::cache(DfgVertex* vtxp) {
    switch (vtxp->type()) {
#define VERTEX_CACHE_ADD_CASE(t) \
    case t::dfgType(): V3DfgCacheInternal::cache(m_cache##t, reinterpret_cast<t*>(vtxp)); break;
        FOREACH_CACHED_VERTEX_TYPE(VERTEX_CACHE_ADD_CASE)
#undef VERTEX_CACHE_ADD_CASE
    default: break;
    }
}

void V3DfgCache::invalidateByValue(DfgVertex* vtxp) {
    switch (vtxp->type()) {
#define VERTEX_CACHE_ADD_CASE(t) \
    case t::dfgType(): \
        V3DfgCacheInternal::invalidateByValue(m_cache##t, reinterpret_cast<t*>(vtxp)); \
        break;
        FOREACH_CACHED_VERTEX_TYPE(VERTEX_CACHE_ADD_CASE)
#undef VERTEX_CACHE_ADD_CASE
    default: break;
    }
}

}  // namespace V3DfgCacheInternal
