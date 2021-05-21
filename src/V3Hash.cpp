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

#include "V3Hash.h"

#include <functional>
#include <iomanip>

V3Hash::V3Hash(const std::string& val)
    : m_value{static_cast<uint32_t>(std::hash<std::string>{}(val))} {}

std::ostream& operator<<(std::ostream& os, const V3Hash& rhs) {
    return os << std::hex << std::setw(8) << std::setfill('0') << rhs.value();
}
