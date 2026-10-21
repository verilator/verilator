// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash calculation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3Hash.h"

#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <sstream>

V3Hash::V3Hash(const std::string& val)
    : m_value{static_cast<uint32_t>(std::hash<std::string>{}(val))} {}

V3Hash::V3Hash(double val) {
    // By value, so +0.0 and -0.0, which compare equal, hash the same
    if (val == 0.0) val = 0.0;
    static_assert(sizeof(double) == sizeof(uint64_t), "Hashing assumes 64-bit double");
    uint64_t bits;
    std::memcpy(&bits, &val, sizeof(bits));
    m_value = V3Hash{bits}.m_value;
}

std::ostream& operator<<(std::ostream& os, const V3Hash& rhs) VL_MT_SAFE {
    return os << 'h' << std::hex << std::setw(8) << std::setfill('0') << rhs.value();
}

std::string V3Hash::toString() const VL_MT_SAFE {
    std::ostringstream os;
    os << *this;
    return os.str();
}
