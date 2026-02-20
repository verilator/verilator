// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// t_compiler_include.h is implicitly included by `--compiler-include`

int dpii_add_check(int actual, int expected) { return actual == expected; }
void dpii_add(int a, int b, int* out) { *out = a + b; }
