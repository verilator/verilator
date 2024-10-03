// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Function traits for metaprogramming
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

#ifndef VERILATOR_V3FUNCTIONTRAITS_H_
#define VERILATOR_V3FUNCTIONTRAITS_H_

#include "verilatedos.h"

#include <cstddef>
#include <tuple>
#include <type_traits>

template <typename T>
struct FunctionTraits;

// For generic types, directly use the result of the signature of its 'operator()'
template <typename T>
struct FunctionTraits final
    : public FunctionTraits<decltype(&std::remove_reference<T>::type::operator())> {};

// Specialization for pointers to member function
template <typename ClassType, typename ReturnType, typename... Args>
struct FunctionTraits<ReturnType (ClassType::*)(Args...) const> VL_NOT_FINAL {
    // Number of arguments
    static constexpr size_t arity = sizeof...(Args);

    // Type of result
    using result_type = ReturnType;

    // Type of arguments
    template <std::size_t I>
    struct arg final {
        using type = typename std::tuple_element<I, std::tuple<Args...>>::type;
    };
};

template <typename T_Callable, size_t index>
struct FunctionArgNoPointerNoCV final {
    using Traits = FunctionTraits<T_Callable>;
    using T_Arg = typename Traits::template arg<index>::type;
    using T_ArgNoPtr = typename std::remove_pointer<T_Arg>::type;
    using type = typename std::remove_cv<T_ArgNoPtr>::type;
};

#endif
