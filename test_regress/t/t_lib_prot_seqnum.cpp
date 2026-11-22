// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Fill every heap allocation with a pattern, so that members the protected
// library fails to initialize read as garbage rather than as fresh zero pages

#include <cstdlib>
#include <cstring>
#include <new>

static void* poisoned(void* p, std::size_t n) {
    if (!p) throw std::bad_alloc{};
    std::memset(p, 0xa5, n);
    return p;
}

void* operator new(std::size_t n) { return poisoned(std::malloc(n ? n : 1), n); }
void* operator new(std::size_t n, std::align_val_t a) {
    const std::size_t al = static_cast<std::size_t>(a);
    // aligned_alloc requires a nonzero size that is a multiple of the alignment
    return poisoned(std::aligned_alloc(al, ((n ? n : 1) + al - 1) / al * al), n);
}
void operator delete(void* p) noexcept { std::free(p); }
void operator delete(void* p, std::size_t) noexcept { std::free(p); }
void operator delete(void* p, std::align_val_t) noexcept { std::free(p); }
void operator delete(void* p, std::size_t, std::align_val_t) noexcept { std::free(p); }
