// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Common include for target specific intrinsics.
///
///     Code using machine specific intrinsics for optimization should
///     include this header rather than directly including he target
///     specific headers. We provide macros to check for availability
///     of instruction sets, and a common mechanism to disable them.
///
//*************************************************************************

#ifndef _VERILATED_INTRINSICS_H_
#define _VERILATED_INTRINSICS_H_ 1  ///< Header Guard

// clang-format off

// Define VL_PORTABLE_ONLY to disable all target specific implementations
#ifndef VL_PORTABLE_ONLY
# ifdef __x86_64__
#  define VL_X86_64 1
# endif
# ifdef __SSE2__
#  define VL_HAVE_SSE2 1
#  include <emmintrin.h>
# endif
# ifdef __AVX2__
#  define VL_HAVE_AVX2 1
#  include <immintrin.h>
# endif
// Recommended reference for x86 intrinsics:
// https://software.intel.com/sites/landingpage/IntrinsicsGuide/
#endif // VL_PORTABLE_ONLY

// clang-format on

#endif  // Guard
