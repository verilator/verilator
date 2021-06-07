// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash calculation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3HASH_H_
#define VERILATOR_V3HASH_H_

#include <cstdint>
#include <string>

//######################################################################
// V3Hash -- Generic hashing

class V3Hash final {
    // A 32-bit hash value. A value of 0 is illegal.
    uint32_t m_value;

public:
    // METHODS
    uint32_t value() const { return m_value; }

    // OPERATORS
    bool operator==(const V3Hash& rh) const { return m_value == rh.m_value; }
    bool operator!=(const V3Hash& rh) const { return m_value != rh.m_value; }
    bool operator<(const V3Hash& rh) const { return m_value < rh.m_value; }
    V3Hash operator+(uint32_t value) const {
        const uint64_t prod = (static_cast<uint64_t>(m_value) * 31) + value;
        return V3Hash(static_cast<uint32_t>(prod ^ (prod >> 32)));
    }
    V3Hash operator+(int32_t value) const { return *this + static_cast<uint32_t>(value); }
    V3Hash operator+(const V3Hash& that) const { return *this + that.m_value; }

    V3Hash& operator+=(const V3Hash& that) {
        *this = *this + that.m_value;
        return *this;
    }
    V3Hash& operator+=(uint32_t value) { return *this += V3Hash(value); }
    V3Hash& operator+=(int32_t value) { return *this += V3Hash(value); }
    V3Hash& operator+=(const std::string& that) { return *this += V3Hash(that); }

    // CONSTRUCTORS
    V3Hash()
        : m_value{1} {}
    explicit V3Hash(uint32_t val)
        : m_value{val | 1} {}
    explicit V3Hash(int32_t val)
        : m_value{static_cast<uint32_t>(val)} {}
    explicit V3Hash(const std::string& val);
};

std::ostream& operator<<(std::ostream& os, const V3Hash& rhs);

#endif  // Guard
