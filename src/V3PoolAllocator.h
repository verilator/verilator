// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Chunked pool allocator
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

#ifndef VERILATOR_V3POOLALLOCATOR_H_
#define VERILATOR_V3POOLALLOCATOR_H_

#include "config_build.h"
#include "verilatedos.h"

#include <cstddef>
#include <memory>
#include <new>
#include <utility>
#include <vector>

// Hands out elements of a single type, allocated 'N_ChunkSize' at a time for
// efficiency. Released elements are recycled via a free list stored in the
// same storage. All memory is released when the pool is destroyed, so the
// elements it handed out must not be used beyond its lifetime, and must all
// have been released by then.
template <typename T_Elem, size_t N_ChunkSize = 128>
class PoolAllocator final {
    static_assert(N_ChunkSize > 0, "Chunk size must be non-zero");

    // A slot of storage, holding either a live element, or a link in the free list.
    union Slot final {
        T_Elem m_elem;  // Storage for the allocated element
        Slot* m_nextFreep;  // Link to the next free slot
        Slot() {}
        ~Slot() {}
    };

    // MEMBERS
    Slot* m_freep = nullptr;  // Head of the free list
    std::vector<std::unique_ptr<Slot[]>> m_allocated;  // The allocated chunks

public:
    // CONSTRUCTORS
    PoolAllocator() = default;
    VL_UNCOPYABLE(PoolAllocator);
    VL_UNMOVABLE(PoolAllocator);

    // METHODS
    // Allocate an element, constructed with the given arguments
    template <typename... Args>
    T_Elem* alloc(Args&&... args) {
        // If no free slots available, then make some
        if (!m_freep) {
            // Allocate in chunks for efficiency
            m_allocated.emplace_back(new Slot[N_ChunkSize]);
            // Chain the new slots into the free list
            Slot* const chunkp = m_allocated.back().get();
            for (size_t i = 1; i < N_ChunkSize; ++i) chunkp[i - 1].m_nextFreep = &chunkp[i];
            chunkp[N_ChunkSize - 1].m_nextFreep = nullptr;
            m_freep = chunkp;
        }
        // Free slots are available, pick up the first one
        Slot* const slotp = m_freep;
        m_freep = slotp->m_nextFreep;
        return new (&slotp->m_elem) T_Elem{std::forward<Args>(args)...};
    }

    // Destroy an element, and return its slot for future allocation
    void free(T_Elem* elemp) {
        elemp->~T_Elem();
        Slot* const slotp = reinterpret_cast<Slot*>(elemp);
        slotp->m_nextFreep = m_freep;
        m_freep = slotp;
    }
};

#endif  // Guard
