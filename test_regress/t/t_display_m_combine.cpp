// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
//*************************************************************************

#include "Vt_display_m_combine__Dpi.h"
#include "svdpi.h"

#include <cstdio>

// These named blocks are DPI scopes only because they contain a %m
void dpic_scopes() {
    static const char* const namesp[] = {"t.u1.named", "t.u10.named"};
    for (const char* namep : namesp) {
        const svScope scope = svGetScopeFromName(namep);
        printf("%s: %s\n", namep, scope ? svGetNameFromScope(scope) : "<none>");
    }
}
