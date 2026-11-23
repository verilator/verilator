#pragma once

#include <utility>
#include <typeinfo>
#include <type_traits>
#include <iostream>
#include <typeinfo>

#include <cstdlib>
#include <memory>

// Introducing namespace Meta, which shall contain all functions used for template meta programming

namespace Meta {
    template<typename T>
    struct is_unsigned {
        constexpr static bool value = std::bool_constant<T(0) < T(-1)>::value;
    };

    // ID

    template<typename T>
    struct ID {
        using Type = T;
    };

    // TRUE & FALSE

    struct True {
        constexpr static bool Value = true;
    };

    struct False {
        constexpr static bool Value = false;
    };

    template<typename T>
    struct FalseIfInstantiated {
        constexpr static bool Value = false;
    };

    // EQUALS

    namespace Implementation {
        template<typename T, typename U>
        struct Equals : False {};

        template<typename T>
        struct Equals<T, T> : True {};
    } // namespace Implementation

    template<typename T, typename U>
    inline constexpr bool Equals() {
        return Implementation::Equals<T, U>::Value;
    }

    // IF THEN ELSE

    namespace Implementation {
        template<bool CONDITION, typename IF_TYPE, typename ELSE_TYPE>
        struct If {
            using Type = ELSE_TYPE;
        };

        template<typename IF_TYPE, typename ELSE_TYPE>
        struct If<true, IF_TYPE, ELSE_TYPE> {
            using Type = IF_TYPE;
        };
    } // namespace Implementation

    template<bool CONDITION, typename IF_TYPE, typename ELSE_TYPE>
    using IF = typename Implementation::If<CONDITION, IF_TYPE, ELSE_TYPE>::Type;

    // LIST

    template<typename... VALUES>
    struct List {
        using Type = List<VALUES...>;
        constexpr static size_t Size = sizeof...(VALUES);
    };


    // LIST CONTAINS

    namespace Implementation {
        template<typename T, typename LIST>
        struct Contains;

        template<typename T>
        struct Contains<T, List<>> : False {};

        template<typename T, typename HEAD, typename... TAIL>
        struct Contains<T, List<HEAD, TAIL...>> : IF<!Meta::Equals<T, HEAD>(), Contains<T, List<TAIL...>>, True> {};
    } // namespace Implementation

    template<typename T, typename LIST>
    inline constexpr bool Contains() {
        return Implementation::Contains<T, LIST>::Value;
    }

} // namespace Meta
