// DESCRIPTION: Verilator: Static assertion termination in a compiler worker
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "V3Ast.h"
#include "V3ThreadPool.h"

V3Global v3Global;

int main(int argc, char** argv) {
    V3MutexConfig::s().configure(true);
    v3Global.boot();
    v3Global.threadPoolp(new V3ThreadPool{2});
    int value = 0;
    const auto convert = [&]() {
        const VNUser integer{uint64_t{42}};
        const VNUser pointer{&value};
        UASSERT_STATIC(integer.toUQuad() == 42 && pointer.to<void*>() == &value,
                       "Valid user-slot conversions changed.");
#ifdef VL_USER_TYPE_CHECKS
        if (argc > 1) {
            if (argv[1][0] == 'p') {
                (void)integer.to<void*>();
            } else if (argv[1][0] == 'i') {
                (void)pointer.toUQuad();
            }
        }
#endif
        UASSERT_STATIC(argc == 1 || argv[1][0] != 'd', "Static assertion failed in worker.");
    };
    {
        V3ThreadScope scope;
        scope.enqueue(convert);
    }
    v3Global.shutdown();
    return 0;
}
