// DESCRIPTION: Verilator: Static assertion and checked user-slot selftest
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#define VL_USER_TYPE_CHECKS
#include "V3Ast.h"

#include <thread>

int main(int argc, char** argv) {
    int value = 0;
    const VNUser empty{};
    const VNUser integer{uint64_t{42}};
    const VNUser pointer{&value};
    UASSERT_STATIC(empty.toUQuad() == 0 && empty.to<void*>() == nullptr, "Cleared slot changed");
    UASSERT_STATIC(integer.toUQuad() == 42 && pointer.to<void*>() == &value,
                   "Valid user-slot conversion changed");
    if (argc == 1) return 0;
    if (argv[1][0] == 'p') {
        (void)integer.to<void*>();
    } else if (argv[1][0] == 'w') {
        std::thread worker{[&]() { (void)pointer.toUQuad(); }};
        worker.join();
    } else {
        (void)pointer.toUQuad();
    }
    return 1;  // A wrong-kind conversion must terminate before returning.
}
