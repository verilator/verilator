// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2021 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include VM_PREFIX_INCLUDE
#include <cassert>
#include <iostream>

int main(int argc, char* argv[]) {
    VM_PREFIX* const tb = new VM_PREFIX;

    tb->instr_i = 0x08c0006f;
    tb->eval();

    std::cout << "tb->illegal_instr_o: " << static_cast<int>(tb->illegal_instr_o) << std::endl
              << std::flush;
    assert(tb->illegal_instr_o == 0);

    delete tb;
    return 0;
}
