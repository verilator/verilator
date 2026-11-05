// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
//*************************************************************************

#include "svdpi.h"

// The name of the scope of the caller
extern "C" const char* dpic_scope() { return svGetNameFromScope(svGetScope()); }

extern "C" int dpic_add1(int v) { return v + 1; }
