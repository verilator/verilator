// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
#include "Vt_dpi_decl__Dpi.h"

char* func(const char* arg) {
    static char str[] = "abc";
    return str;
}
// some functions (e.g. getenv() from glibc) may have additional specifier, lack of it in the
// declaration will cause build errors
char* func_with_specifier(const char* arg) throw() {
    static char str[] = "efd";
    return str;
}
