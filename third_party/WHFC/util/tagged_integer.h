#pragma once

#include <cassert>
#include <iostream>
#include <sstream>
#include "meta.h"

template<int TAG, typename VALUE_TYPE, VALUE_TYPE INVALID, VALUE_TYPE DEFAULT = INVALID, typename... ADDITIONAL_CASTS>
class TaggedInteger {

public:
    using ValueType = VALUE_TYPE;
    constexpr static ValueType InvalidValue = INVALID;
    constexpr static ValueType DefaultValue = DEFAULT;
    using AdditionalCasts = Meta::List<ADDITIONAL_CASTS...>;
    using Type = TaggedInteger<TAG, ValueType, InvalidValue, DefaultValue, ADDITIONAL_CASTS...>;

public:
    constexpr TaggedInteger() : internalValue(DefaultValue) {}

    constexpr explicit TaggedInteger(const ValueType& value) : internalValue(value) {}

    constexpr inline operator const ValueType&() const noexcept { return internalValue; }

    template<typename T, typename = typename std::enable_if_t<Meta::Contains<T, AdditionalCasts>()>>
    constexpr inline operator T() const noexcept {
        return T(internalValue);
    }

    constexpr inline ValueType& value() noexcept {
        assert(isValid());
        return internalValue;
    }

    constexpr inline const ValueType& value() const noexcept { return internalValue; }

    template<typename OtherValueType>
    static inline Type fromOtherValueType(OtherValueType x) {
        return Type(static_cast<OtherValueType>(x));
    }

    constexpr static Type Invalid() { return TaggedInteger(InvalidValue); }

    inline bool isValid() const noexcept { return internalValue != InvalidValue; }
    inline bool isInvalid() const noexcept { return internalValue == InvalidValue; }
    inline void invalidate() noexcept { internalValue = InvalidValue; }

    constexpr inline bool operator<(const Type& other) const noexcept { return internalValue < other.internalValue; }
    inline bool operator>(const Type& other) const noexcept { return internalValue > other.internalValue; }
    inline bool operator<=(const Type& other) const noexcept { return internalValue <= other.internalValue; }
    inline bool operator>=(const Type& other) const noexcept { return internalValue >= other.internalValue; }
    inline bool operator==(const Type& other) const noexcept { return internalValue == other.internalValue; }
    inline bool operator!=(const Type& other) const noexcept { return internalValue != other.internalValue; }

    inline Type& operator+=(const Type& other) noexcept {
        assert(isValid());
        assert(other.isValid());
        internalValue += other.internalValue;
        return *this;
    }

    inline Type& operator+=(const ValueType& other) noexcept {
        assert(isValid());
        internalValue += other;
        return *this;
    }

    inline Type& operator-=(const Type& other) noexcept {
        assert(isValid());
        assert(other.isValid());
        internalValue -= other.internalValue;
        return *this;
    }
    inline Type& operator-=(const ValueType& other) noexcept {
        assert(isValid());
        internalValue -= other;
        return *this;
    }

    inline Type& operator*=(const Type& other) noexcept {
        assert(isValid());
        assert(other.isValid());
        internalValue *= other.internalValue;
        return *this;
    }
    inline Type& operator*=(const ValueType& other) noexcept {
        assert(isValid());
        internalValue *= other;
        return *this;
    }

    inline Type& operator/=(const Type& other) noexcept {
        assert(isValid());
        assert(other.isValid());
        internalValue /= other.internalValue;
        return *this;
    }
    inline Type& operator/=(const ValueType& other) noexcept {
        assert(isValid());
        internalValue /= other;
        return *this;
    }

    inline Type operator+(const Type& other) const noexcept {
        assert(isValid());
        assert(other.isValid());
        return Type(internalValue + other.internalValue);
    }

    inline Type operator-() const noexcept {
        assert(isValid());
        return Type(-internalValue);
    }

    inline Type operator-(const Type& other) const noexcept {
        assert(isValid());
        assert(other.isValid());
        return Type(internalValue - other.internalValue);
    }

    inline Type operator*(const Type& other) const noexcept {
        assert(isValid());
        assert(other.isValid());
        return Type(internalValue * other.internalValue);
    }

    inline Type operator/(const Type& other) const noexcept {
        assert(isValid());
        assert(other.isValid());
        return Type(internalValue / other.internalValue);
    }

    inline Type operator%(const Type& other) const noexcept {
        assert(isValid());
        assert(other.isValid());
        return Type(internalValue % other.internalValue);
    }

    inline Type& operator++() noexcept {
        assert(isValid());
        internalValue++;
        return *this;
    }

    inline Type operator++(int) noexcept {
        assert(isValid());
        internalValue++;
        return Type(internalValue - 1);
    }

    inline Type& operator*() noexcept { return *this; }

    inline Type& operator--() noexcept {
        assert(isValid());
        internalValue--;
        return *this;
    }

    inline Type operator--(int) noexcept {
        assert(isValid());
        internalValue--;
        return Type(internalValue + 1);
    }

    inline friend std::istream& operator>>(std::istream& in, Type& type) noexcept {
        in >> type.internalValue;
        return in;
    }

    inline friend std::ostream& operator<<(std::ostream& out, const Type& type) noexcept {
        if (type.isValid()) {
            return out << type.internalValue;
        } else {
            return out << "Invalid";
        }
    }

    inline friend std::string operator+(const std::string& string, const Type& type) noexcept {
        std::stringstream result;
        result << string << type;
        return result.str();
    }

    inline friend std::string operator+(const char string[], const Type& type) noexcept {
        std::stringstream result;
        result << string << type;
        return result.str();
    }

private:
    ValueType internalValue;
};

template<int TAG, typename DEPENDENCE>
using DependentTaggedInteger = TaggedInteger<TAG, typename DEPENDENCE::ValueType, DEPENDENCE::InvalidValue, DEPENDENCE::DefaultValue, DEPENDENCE>;
