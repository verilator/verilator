// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simple and efficient Run-Time Type Information
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

#ifndef VERILATOR_V3RTTI_H_
#define VERILATOR_V3RTTI_H_

#include "verilatedos.h"

#include <cstdint>
#include <type_traits>

// Holds list of types as template parameter pack.
// Useful in compile-time code generation.
template <typename... TN>
struct VTypeList {
    template <typename... UN>
    constexpr VTypeList<TN..., UN...> operator+(VTypeList<UN...>) const {
        return {};
    }
};

// Holds one type.
// Can be safely used as a return or argument type, and even instantiated, without triggering any
// potential limitations or effects of the held type.
template <typename T>
struct VTypeWrapper {
    using type_t = T;
};

// Implementation details of other constructs defined in this header.
namespace V3RttiInternal {

// Helper function for extracting first type from VTypeList.
template <typename T0, typename... TN>
static inline constexpr VTypeWrapper<T0> vlTypeListFront(VTypeList<T0, TN...>) {
    return {};
}

// Overload for empty type list. Returns false.
inline static constexpr bool isClassIdOfOneOf(uintptr_t id, VTypeList<>) VL_PURE { return false; }

// Returns true iff `id` has the same value as `T::rttiClassId()`, where `T` is any type held by
// `VTypeList` object passed as the second argument.
template <typename Base0, typename... BaseN>
inline static constexpr bool isClassIdOfOneOf(uintptr_t id, VTypeList<Base0, BaseN...>) VL_PURE {
    return id == Base0::rttiClassId() || isClassIdOfOneOf(id, VTypeList<BaseN...>{});
}

}  // namespace V3RttiInternal

// Alias for the first (frontmost) type held by type list `TL`.
template <typename TL>
using VTypeListFront = typename decltype(::V3RttiInternal::vlTypeListFront(TL{}))::type_t;

// `VTypeList` holding types from type lists `TL1` followed by types from type list `TL2`.
template <typename TL1, typename TL2>
using VJoinedTypeLists = decltype(TL1{} + TL2{});

// Common code used by VL_RTTI_COMMON_IMPL and VL_RTTI_COMMON_IMPL_BASE.
#define V3RTTIINTERNAL_VL_RTTI_COMMON_IMPL(ThisClass) \
private: \
    /* A type used only for implementation of the static_assert below. */ \
    struct RttiUniqueTypeForThisClass {}; \
    static_assert( \
        std::is_same<RttiUniqueTypeForThisClass, ThisClass::RttiUniqueTypeForThisClass>::value, \
        "'ThisClass' argument (" #ThisClass ") does not match the class name"); \
\
public: \
    /* Returns unique ID of the class. Useful with `isInstanceOfClassWithId()` method. */ \
    static uintptr_t rttiClassId() VL_PURE { \
        /* The only purpose of the following variable is to occupy an unique memory address. */ \
        /* This address is used as an unique class ID. */ \
        static char aStaticVariable; \
        return reinterpret_cast<uintptr_t>(&aStaticVariable); \
    }

// Call this macro at the beginning of class definition if the class derives from a
// class with VL_RTTI_IMPL or VL_RTTI_IMPL_BASE calls.
#define VL_RTTI_IMPL(ThisClass, DirectBaseClass) \
    V3RTTIINTERNAL_VL_RTTI_COMMON_IMPL(ThisClass) \
    static_assert( \
        std::is_same<DirectBaseClass, \
                     VTypeListFront<DirectBaseClass::RttiThisAndBaseClassesList>>::value, \
        "Missing VL_RTTI_IMPL(...) in the direct base class (" #DirectBaseClass ")"); \
\
public: \
    /* Type list containing this class and all classes from the inheritance chain. */ \
    using RttiThisAndBaseClassesList \
        = VJoinedTypeLists<VTypeList<ThisClass>, \
                           typename DirectBaseClass::RttiThisAndBaseClassesList>; \
\
protected: \
    /* Returns true iff `id` has the same value as `T::rttiClassId()`, where `T` is either this \
     * class or any class from this class' inheritance chain. */ \
    bool isInstanceOfClassWithId(uintptr_t id) const override VL_PURE { \
        return ::V3RttiInternal::isClassIdOfOneOf(id, RttiThisAndBaseClassesList{}); \
    } \
\
private: /* Revert to private visibility after this macro */

// Call this macro at the beginning of a base class to implement class type queries using
// `p->isInstanceOfClassWithId(ClassName::rttiClassId())`.
#define VL_RTTI_IMPL_BASE(ThisClass) \
    V3RTTIINTERNAL_VL_RTTI_COMMON_IMPL(ThisClass) \
public: \
    /* Type list containing this class and all classes from the inheritance chain. */ \
    using RttiThisAndBaseClassesList = VTypeList<ThisClass>; \
\
protected: \
    /* Returns true iff `id` has the same value as value returned by this class' \
       `rttiClassId()` method. */ \
    virtual bool isInstanceOfClassWithId(uintptr_t id) const VL_PURE { \
        return id == rttiClassId(); \
    } \
\
private: /* Revert to private visibility after this macro */

#endif  // Guard
