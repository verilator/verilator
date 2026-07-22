// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilator common target-specific intrinsics header
///
/// This file is not part of the Verilated public-facing API.
///
/// It is only for internal use; code using machine-specific intrinsics for
/// optimization should include this header rather than directly including
/// the target-specific headers. We provide macros to check for availability
/// of instruction sets, and a common mechanism to disable them.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_INTRINSICS_H_
#define VERILATOR_VERILATED_INTRINSICS_H_

// clang-format off

// Use VL_PORTABLE_ONLY to disable all intrinsics based optimization
#ifndef VL_PORTABLE_ONLY
# if defined(__SSE2__) && !defined(VL_DISABLE_SSE2)
#  define VL_HAVE_SSE2 1
#  include <emmintrin.h>
# endif
# if defined(__AVX2__) && defined(VL_HAVE_SSE2) && !defined(VL_DISABLE_AVX2)
#  define VL_HAVE_AVX2 1
#  include <immintrin.h>
# endif
# if defined(__LZCNT__) && !defined(VL_DISABLE_LZCNT)
#  define VL_HAVE_LZCNT 1
#  ifndef VL_HAVE_AVX2
#   include <immintrin.h>
#  endif
# endif
#endif

// clang-format on

VL_ATTR_ALWINLINE int vlIntrinClz32(uint32_t value) {
    VL_DEBUG_IFDEF(assert(value););
#ifdef VL_HAVE_LZCNT
    return static_cast<int>(_lzcnt_u32(value));
#elif (defined(__GNUC__) || defined(__clang__)) && !defined(VL_NO_BUILTINS)
    return __builtin_clz(value);
#else
    int zeros = 0;
    uint32_t bit = 1U << 31;
    while (!(value & bit)) {
        ++zeros;
        bit >>= 1;
    }
    return zeros;
#endif
}

VL_ATTR_ALWINLINE int vlIntrinClz64(uint64_t value) {
    VL_DEBUG_IFDEF(assert(value););
#if defined(VL_HAVE_LZCNT) && (defined(__x86_64__) || defined(_M_X64))
    return static_cast<int>(_lzcnt_u64(value));
#elif (defined(__GNUC__) || defined(__clang__)) && !defined(VL_NO_BUILTINS)
    return __builtin_clzll(static_cast<unsigned long long>(value));
#else
    const uint32_t upper = static_cast<uint32_t>(value >> 32);
    return upper ? vlIntrinClz32(upper) : 32 + vlIntrinClz32(static_cast<uint32_t>(value));
#endif
}

#endif  // Guard
