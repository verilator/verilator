// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include <cstdio>
#include <cstring>
#include "svdpi.h"

#ifdef _WIN32
# define T_PRI64 "I64"
#else // Linux or compliant Unix flavors
# define T_PRI64 "ll"
#endif

//======================================================================

#if defined(VERILATOR)
# include "Vt_dpi_export__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS

extern "C" {
    extern int dpix_run_tests();

    extern int dpix_t_int(int i, int* o);
    extern int dpix_t_renamed(int i, int* o);

    extern int dpix_int123();

    extern unsigned char dpix_f_bit(unsigned char i);
    extern int           dpix_f_int(int i);
    extern char          dpix_f_byte(char i);
    extern short int     dpix_f_shortint(short int i);
    extern long long     dpix_f_longint(long long i);
    extern void*         dpix_f_chandle(void* i);

    extern int dpix_sub_inst (int i);
}

#endif

//======================================================================

#define CHECK_RESULT(type, got, exp)		\
    if ((got) != (exp)) { 			\
	printf("%%Error: %s:%d:", __FILE__,__LINE__);	\
	union { type a; long long l; } u;	\
	u.l = 0; u.a = got;			\
	printf(" GOT = %" T_PRI64 "x", u.l);	\
	u.l = 0; u.a = exp;			\
	printf("  EXP = %" T_PRI64 "x\n", u.l); \
	return __LINE__; \
    }
#define CHECK_RESULT_NNULL(got) \
    if (!(got)) { \
	printf("%%Error: %s:%d: GOT = %p   EXP = !NULL\n", __FILE__,__LINE__, (got)); \
	return __LINE__; \
    }

static int check_sub(const char* name, int i) {
    svScope scope = svGetScopeFromName(name);
#ifdef TEST_VERBOSE
    printf("svGetScopeFromName(\"%s\") -> %p\n", name, scope);
#endif
    CHECK_RESULT_NNULL (scope);
    svScope prev = svGetScope();
    svScope sout = svSetScope(scope);
    CHECK_RESULT(svScope, sout, prev);
    CHECK_RESULT(svScope, svGetScope(), scope);
    int out = dpix_sub_inst(100*i);
    CHECK_RESULT(int, out, 100*i + i);

    return 0; // OK
}

// Called from our Verilog code to run the tests
int dpix_run_tests() {
    printf("dpix_run_tests:\n");

#ifdef VERILATOR
    static int didDump = 0;
    if (didDump++ == 0) {
# ifdef TEST_VERBOSE
	Verilated::internalsDump();
# endif
    }
#endif

#ifndef CADENCE // Unimplemented; how hard is it?
    printf ("svDpiVersion: %s\n",svDpiVersion());
    CHECK_RESULT (bool,
		  strcmp(svDpiVersion(), "1800-2005")==0
		  || strcmp(svDpiVersion(), "P1800-2005")==0
		  , 1);
#endif

    CHECK_RESULT (int, dpix_int123(), 0x123 );

#ifndef CADENCE  // No export calls from an import
    int o;
    dpix_t_int(0x456, &o);
    CHECK_RESULT (unsigned long, o, ~0x456UL);

    dpix_t_renamed(0x456, &o);
    CHECK_RESULT (int, o, 0x458UL);
#endif

    svBitVecVal vec10[1] = {0x10};

    CHECK_RESULT (int, dpix_f_bit(1), 0x0);
    CHECK_RESULT (int, dpix_f_bit(0), 0x1);
    CHECK_RESULT (int, dpix_f_bit15(vec10) & 0x7fUL, 0x6f);
    // Simulators disagree over the next three's sign extension unless we mask the upper bits
    CHECK_RESULT (int, dpix_f_int(1) & 0xffffffffUL, 0xfffffffeUL);
    CHECK_RESULT (int, dpix_f_byte(1) & 0xffUL, 0xfe);
    CHECK_RESULT (int, dpix_f_shortint(1) & 0xffffUL, 0xfffeUL);

    CHECK_RESULT (unsigned long long, dpix_f_longint(1), 0xfffffffffffffffeULL);
    CHECK_RESULT (void*, dpix_f_chandle((void*)(12345)), (void*)(12345));

    {
	svBitVecVal i_vec95[3] = {0x72912312,0xab782a12,0x8a413bd9};
	svBitVecVal o_vec95[3] = {0,0,0};
	dpix_t_bit95(i_vec95, o_vec95);
	CHECK_RESULT(int, o_vec95[0], ~i_vec95[0]);
	CHECK_RESULT(int, o_vec95[1], ~i_vec95[1]);
	CHECK_RESULT(int, o_vec95[2], (~i_vec95[2])&0x7fffffffUL);
    }
    {
	svBitVecVal i_vec96[3] = {0xf2912312,0xab782a12,0x8a413bd9};
	svBitVecVal o_vec96[3] = {0,0,0};
	dpix_t_bit96(i_vec96, o_vec96);
	CHECK_RESULT(int, o_vec96[0], ~i_vec96[0]);
	CHECK_RESULT(int, o_vec96[1], ~i_vec96[1]);
	CHECK_RESULT(int, o_vec96[2], ~i_vec96[2]);
    }

    if (int bad=check_sub("top.t.a",1)) return bad;
    if (int bad=check_sub("top.t.b",2)) return bad;

    return -1;  // OK status
}
