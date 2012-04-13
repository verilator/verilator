// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//*************************************************************************

#include <cstdio>
#include <cstring>
#include "svdpi.h"

//======================================================================

#include "Vt_dpi_qw__Dpi.h"

//======================================================================

// Called from our Verilog code to run the tests
void poke_value(int i) {
    printf("poke_value(%d)\n", i);

#ifdef VERILATOR
    static int didDump = 0;
    if (didDump++ == 0) {
# ifdef TEST_VERBOSE
	Verilated::scopesDump();
# endif
    }
#endif

    svScope scope = svGetScopeFromName("top.t.a");
    if (scope == NULL) {
        printf("%%Error: null scope for top.t.a\n");
        return;
    }

    svSetScope(scope);
    svBitVecVal val[2];
    val[0] = i;
    val[1] = 0;
    set_value(val);
}
