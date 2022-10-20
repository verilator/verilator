// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Backports of features from future C++ versions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3STDFUTURE_H_
#define VERILATOR_V3STDFUTURE_H_

#include <functional>

namespace vlstd {

// constexpr std::max with arguments passed by value (required by constexpr before C++14)
template <class T>
constexpr T max(T a, T b) {
    return a > b ? a : b;
}

// C++17 is_invocable
template <typename F, typename... Args>
struct is_invocable
    : std::is_constructible<std::function<void(Args...)>,
                            std::reference_wrapper<typename std::remove_reference<F>::type>> {};

// C++17 is_invocable_r
template <typename R, typename F, typename... Args>
struct is_invocable_r
    : std::is_constructible<std::function<R(Args...)>,
                            std::reference_wrapper<typename std::remove_reference<F>::type>> {};
};  // namespace vlstd

#endif  // Guard
