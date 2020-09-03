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
#include <cstring>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# include "Vt_dpi_import__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

typedef struct {
    int a;
    int b;
} substruct_t;

#ifdef NEED_EXTERNS
extern "C" {
    // If get ncsim: *F,NOFDPI: Function {foo} not found in default libdpi.
    // Then probably forgot to list a function here.

    extern unsigned char dpii_f_bit     (unsigned char i);
    extern svBitVecVal   dpii_f_bit8    (const svBitVecVal* i);
    extern svBitVecVal   dpii_f_bit9    (const svBitVecVal* i);
    extern svBitVecVal   dpii_f_bit16   (const svBitVecVal* i);
    extern svBitVecVal   dpii_f_bit17   (const svBitVecVal* i);
    extern svBitVecVal   dpii_f_bit32   (const svBitVecVal* i);
    extern long long     dpii_f_bit33   (const svBitVecVal* i);
    extern long long     dpii_f_bit64   (const svBitVecVal* i);
    extern long long     dpii_f_bit95   (const svBitVecVal* i, svBitVecVal* o);
    extern int           dpii_f_int     (int i);
    extern char          dpii_f_byte    (char i);
    extern short int     dpii_f_shortint(short int i);
    extern long long     dpii_f_longint (long long i);
    extern void*         dpii_f_chandle (void* i);
    extern const char*   dpii_f_string  (const char* i);
    extern double        dpii_f_real    (double i);
    extern float         dpii_f_shortreal(float i);

    extern void dpii_v_bit      (unsigned char i, unsigned char* o);
    extern void dpii_v_int      (int i,         int *o);
    extern void dpii_v_uint     (unsigned int i, unsigned int *o);
    extern void dpii_v_byte     (char i,        char *o);
    extern void dpii_v_shortint (short int i,   short int *o);
    extern void dpii_v_ushort   (unsigned short i, unsigned short *o);
    extern void dpii_v_longint  (long long i,   long long *o);
    extern void dpii_v_ulong    (unsigned long long i, unsigned long long *o);
    extern void dpii_v_struct   (const svBitVecVal* i, svBitVecVal* o);
    extern void dpii_v_substruct        (const svBitVecVal* i, int* o);
    extern void dpii_v_chandle  (void* i,       void* *o);
    extern void dpii_v_string   (const char* i, const char** o);
    extern void dpii_v_real     (double i,      double* o);
    extern void dpii_v_shortreal(float i,       float* o);

    extern void dpii_v_struct   (const svBitVecVal* i, svBitVecVal* o);
    extern void dpii_v_substruct        (const svBitVecVal* i, int* o);
    extern void dpii_v_bit64(const svBitVecVal* i, svBitVecVal* o);
    extern void dpii_v_bit95(const svBitVecVal* i, svBitVecVal* o);
    extern void dpii_v_bit96(const svBitVecVal* i, svBitVecVal* o);

    extern void dpii_v_reg(unsigned char i, unsigned char* o);
    extern void dpii_v_reg15(const svLogicVecVal* i, svLogicVecVal* o);
    extern void dpii_v_reg95(const svLogicVecVal* i, svLogicVecVal* o);
    extern void dpii_v_integer(const svLogicVecVal* i, svLogicVecVal* o);
    extern void dpii_v_time(const svLogicVecVal* i, svLogicVecVal* o);

    extern int dpii_f_strlen(const char* i);

    extern void dpii_f_void();
    extern int dpii_t_void();
    extern int dpii_t_void_context();
    extern int dpii_t_int(int i, int *o);

    extern int dpii_fa_bit(int i);
}
#endif

//======================================================================

unsigned char   dpii_f_bit (unsigned char i)            { return 0x1 & ~i; }
svBitVecVal     dpii_f_bit8 (const svBitVecVal *i)      { return 0xffUL & ~*i; }
svBitVecVal     dpii_f_bit9 (const svBitVecVal *i)      { return 0x1ffUL & ~*i; }
svBitVecVal     dpii_f_bit16(const svBitVecVal *i)      { return 0xffffUL & ~*i; }
svBitVecVal     dpii_f_bit17(const svBitVecVal *i)      { return 0x1ffffUL & ~*i; }
svBitVecVal     dpii_f_bit32(const svBitVecVal *i)      { return               ~*i; }
long long       dpii_f_bit33(const svBitVecVal *i)      { return ((1ULL<<33)-1) & ~((long long)(i[1])<<32ULL | i[0]); }
long long       dpii_f_bit64(const svBitVecVal *i)      { return ~((long long)(i[1])<<32ULL | i[0]); }

int             dpii_f_int     (int i)          { return ~i; }
char            dpii_f_byte    (char i)         { return ~i; }
short int       dpii_f_shortint(short int i)    { return ~i; }
long long       dpii_f_longint (long long i)    { return ~i; }
void*           dpii_f_chandle (void* i)        { return i; }
const char*     dpii_f_string  (const char* i)  { return i; }
double          dpii_f_real    (double i)       { return i+1.5; }
float           dpii_f_shortreal(float i)       { return i+1.5f; }

void dpii_v_bit(unsigned char i, unsigned char *o)      { *o = 1 & ~i; }
void dpii_v_int(int i, int *o)                          { *o = ~i; }
void dpii_v_uint(unsigned int i, unsigned int *o)       { *o = ~i; }
void dpii_v_byte(char i, char *o)                       { *o = ~i; }
void dpii_v_shortint(short int i, short int *o) { *o = ~i; }
void dpii_v_ushort(unsigned short i, unsigned short *o) { *o = ~i; }
void dpii_v_longint(long long i, long long *o)          { *o = ~i; }
void dpii_v_ulong(unsigned long long i, unsigned long long *o)  { *o = ~i; }
void dpii_v_chandle(void* i, void* *o)                  { *o = i; }
void dpii_v_string(const char* i, const char** o)       { *o = strdup(i); }  // Leaks
void dpii_v_real(double i, double* o)                   { *o = i + 1.5; }
void dpii_v_shortreal(float i, float* o)                { *o = i + 1.5f; }

void dpii_v_reg(unsigned char i, unsigned char* o) { *o = (~i)&1; }
void dpii_v_reg15(const svLogicVecVal* i, svLogicVecVal* o) {
    o[0].aval = (~i[0].aval) & 0x7fffUL;
    o[0].bval = 0;
}
void dpii_v_reg95(const svLogicVecVal* i, svLogicVecVal* o) {
    o[0].aval = (~i[0].aval);
    o[1].aval = (~i[1].aval);
    o[2].aval = (~i[2].aval) & 0x7fffffffUL;
    o[0].bval = 0;
    o[1].bval = 0;
    o[2].bval = 0;
}
void dpii_v_integer(const svLogicVecVal* i, svLogicVecVal* o) {
    o[0].aval = (~i[0].aval);
    o[0].bval = 0;
}
void dpii_v_time(const svLogicVecVal* i, svLogicVecVal* o) {
    o[0].aval = (~i[0].aval);
    o[1].aval = (~i[1].aval);
    o[0].bval = 0;
    o[1].bval = 0;
}

void dpii_v_struct(const svBitVecVal* i, svBitVecVal* o) {
    o[0] = ~i[0];
    o[1] = ~i[1];
    o[2] = ~i[2];
}
void dpii_v_substruct(const svBitVecVal* i, int* o) {
    // To be most like other tools, this should automagically take the substruct_t
    // as an argument, and not require this cast...
    substruct_t* issp = (substruct_t*)i;
    o[0] = issp->b - issp->a;
}
void dpii_v_bit64(const svBitVecVal* i, svBitVecVal* o) {
    o[0] = ~i[0];
    o[1] = ~i[1];
}
void dpii_v_bit95(const svBitVecVal* i, svBitVecVal* o) {
    o[0] = (~i[0]);
    o[1] = (~i[1]);
    o[2] = (~i[2]) & 0x7fffffffUL;
}
void dpii_v_bit96(const svBitVecVal* i, svBitVecVal* o) {
    o[0] = ~i[0];
    o[1] = ~i[1];
    o[2] = ~i[2];
}

int dpii_f_strlen(const char* i) { return strlen(i); }

//======================================================================

void dpii_f_void() {}

#ifdef VCS
void dpii_t_void() {}
void dpii_t_void_context() {}
void dpii_t_int(int i, int* o) { *o = i; }
#else
int dpii_t_void() { return svIsDisabledState(); }
int dpii_t_void_context() { return svIsDisabledState(); }
int dpii_t_int(int i, int* o) {
    *o = i;
    return svIsDisabledState();  // Tasks generally need this
}
#endif

int dpii_fa_bit(int i) { return ~i; }
