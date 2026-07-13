// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

static_assert(__cplusplus >= EXPECT_CXX_MIN, "The runtime requires C++14 or newer");

int cxx14FloorProbe() {
    const auto identity = [](const auto value) { return value; };
    return identity(14);
}
