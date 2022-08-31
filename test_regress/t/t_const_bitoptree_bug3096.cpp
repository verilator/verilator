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

#include <Vt_const_bitoptree_bug3096.h>
#include <cassert>
#include <iostream>

int main(int argc, char* argv[]) {
    Vt_const_bitoptree_bug3096* const tb = new Vt_const_bitoptree_bug3096;

    tb->instr_i = 0x08c0006f;
    tb->eval();

    std::cout << "tb->illegal_instr_o: " << static_cast<int>(tb->illegal_instr_o) << std::endl
              << std::flush;
    assert(tb->illegal_instr_o == 0);

    delete tb;
    return 0;
}
