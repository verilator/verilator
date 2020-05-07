// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include <cstdio>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# ifdef T_DPI_CONTEXT_NOOPT
#  include "Vt_dpi_context_noopt__Dpi.h"
# else
#  include "Vt_dpi_context__Dpi.h"
# endif
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef VERILATOR
# include "verilated.h"
#endif

#ifdef NEED_EXTERNS
extern "C" {

    extern int dpic_line();
    extern int dpic_save(int value);
    extern int dpic_restore();
    extern unsigned dpic_getcontext();
}
#endif

//======================================================================

int dpic_line() {
    svScope scope = svGetScope();
    if (!scope) {
        printf("%%Warning: svGetScope failed\n");
        return 0;
    }

#ifdef VERILATOR
    static int didDump = 0;
    if (didDump++ == 0) { Verilated::scopesDump(); }
#endif

    const char* scopenamep = svGetNameFromScope(scope);
    if (!scopenamep) {
        printf("%%Warning: svGetNameFromScope failed\n");
        return 0;
    }
    if (scope != svGetScopeFromName(scopenamep)) {
        printf("%%Warning: svGetScopeFromName repeat failed\n");
        return 0;
    }

    const char* filenamep = "";
    int lineno = 0;
    if (svGetCallerInfo(&filenamep, &lineno)) {
        printf("Call from %s:%d:%s\n", filenamep, lineno, scopenamep);
    } else {
        printf("%%Warning: svGetCallerInfo failed\n");
        return 0;
    }
    return lineno;
}

extern int Dpic_Unique;
int Dpic_Unique = 0;  // Address used for uniqueness

int dpic_save(int value) {
    svScope scope = svGetScope();
    if (!scope) {
        printf("%%Warning: svGetScope failed\n");
        return 0;
    }

    // Use union to avoid cast to different size pointer warnings
    union valpack {
        void* ptr;
        int i;
    } vp;

    vp.i = value; if (vp.i) { }
    if (svPutUserData(scope, &Dpic_Unique, vp.ptr)) {
        printf("%%Warning: svPutUserData failed\n");
        return 0;
    }
    return 1;
}

int dpic_restore() {
    svScope scope = svGetScope();
    if (!scope) {
        printf("%%Warning: svGetScope failed\n");
        return 0;
    }

    if (void* userp = svGetUserData(scope, (void*)&Dpic_Unique)) {
        // Use union to avoid cast to different size pointer warnings
        union valpack {
            void* ptr;
            int i;
        } vp;
        vp.ptr = userp;
        return vp.i;
    } else {
        printf("%%Warning: svGetUserData failed\n");
        return 0;
    }
}

unsigned dpic_getcontext() {
    svScope scope = svGetScope();
    printf("%%Info: svGetScope returned scope (%p) with name %s\n",
           scope, svGetNameFromScope(scope));
    return (unsigned)(uintptr_t)scope;
}
