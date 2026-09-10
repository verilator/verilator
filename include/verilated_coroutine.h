// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated/Verilator common header for including coroutines
///
/// This header enables coroutines for both Clang and GCC.
/// It works with libc++ and libstdc++.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_COROUTINE_H_
#define VERILATOR_VERILATED_COROUTINE_H_

// clang-format off
#ifdef _LIBCPP_VERSION  // libc++
# if defined(__has_include) && !__has_include(<coroutine>) && __has_include(<experimental/coroutine>)
#  if __clang_major__ > 13  // Clang > 13 warns that coroutine types in std::experimental are deprecated
#   pragma clang diagnostic push
#   pragma clang diagnostic ignored "-Wdeprecated-experimental-coroutine"
#  endif
#  include <experimental/coroutine>
   namespace std {
       using namespace experimental;  // Bring std::experimental into the std namespace
   }
# else
#  include <coroutine>
# endif
#else
# if defined __clang__ && defined __GLIBCXX__ && !defined __cpp_impl_coroutine
#  define __cpp_impl_coroutine 1  // Clang doesn't define this, but it's needed for libstdc++
# endif
# include <coroutine>
# if __clang_major__ < 14
   namespace std {  // Bring coroutine library into std::experimental, as Clang < 14 expects it to be there
       namespace experimental {
           using namespace std;
       }
   }
# endif
#endif
// clang-format on

#endif
