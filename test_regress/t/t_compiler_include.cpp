// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// t_compiler_include.h is implicitly included by `--compiler-include`

#include <verilated.h>
#include VM_PREFIX_INCLUDE

int main() {
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX;
    topp->in = 123;
    topp->eval();

    if (ext_equal(topp->in, topp->out))
        VL_PRINTF("*-* All Finished *-*\n");
    else
        VL_PRINTF("in (%d) != out (%d)\n", topp->in, topp->out);

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}
