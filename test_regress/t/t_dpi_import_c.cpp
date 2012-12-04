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

#ifdef NEED_EXTERNS
extern "C" {

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

    extern void dpii_v_bit	(unsigned char i, unsigned char* o);
    extern void dpii_v_int	(int i,		int *o);
    extern void dpii_v_uint	(unsigned int i, unsigned int *o);
    extern void dpii_v_byte	(char i,	char *o);
    extern void dpii_v_shortint	(short int i,	short int *o);
    extern void dpii_v_ushort	(unsigned short i, unsigned short *o);
    extern void dpii_v_longint	(long long i,	long long *o);
    extern void dpii_v_ulong	(unsigned long long i, unsigned long long *o);
    extern void dpii_v_chandle	(void* i,	void* *o);
    extern void dpii_v_string   (const char* i, const char** o);
    extern void dpii_v_real     (double i,      double* o);
    extern void dpii_v_shortreal(float i,       float* o);

    extern void dpii_f_void	();
    extern int dpii_t_void	();
    extern int dpii_t_void_context ();
    extern int dpii_t_int	(int i,		int *o);

    extern int dpii_f_strlen (const char* i);

    extern int dpii_fa_bit(int i);
}
#endif

//======================================================================

unsigned char	dpii_f_bit (unsigned char i)		{ return SV_MASK(1) & ~i; }
svBitVecVal	dpii_f_bit8 (const svBitVecVal *i)	{ return SV_MASK(8) & ~*i; }
svBitVecVal	dpii_f_bit9 (const svBitVecVal *i)	{ return SV_MASK(9) & ~*i; }
svBitVecVal	dpii_f_bit16(const svBitVecVal *i)	{ return SV_MASK(16) & ~*i; }
svBitVecVal	dpii_f_bit17(const svBitVecVal *i)	{ return SV_MASK(17) & ~*i; }
svBitVecVal	dpii_f_bit32(const svBitVecVal *i)	{ return               ~*i; }
long long	dpii_f_bit33(const svBitVecVal *i)	{ return ((1ULL<<33)-1) & ~((long long)(i[1])<<32ULL | i[0]); }
long long	dpii_f_bit64(const svBitVecVal *i)	{ return ~((long long)(i[1])<<32ULL | i[0]); }

int		dpii_f_int (int i)		{ return ~i; }
char		dpii_f_byte (char i)		{ return ~i; }
short int	dpii_f_shortint(short int i)	{ return ~i; }
long long	dpii_f_longint (long long i)	{ return ~i; }
void*		dpii_f_chandle (void* i)	{ return i; }
const char*	dpii_f_string  (const char* i)	{ return i; }
double		dpii_f_real    (double i)	{ return i+1.5; }
float		dpii_f_shortreal(float i)	{ return i+1.5; }

void dpii_v_bit	(unsigned char i, unsigned char *o)	{ *o = SV_MASK(1) & ~i; }
void dpii_v_int (int i, int *o)				{ *o = ~i; }
void dpii_v_uint (unsigned int i, unsigned int *o)	{ *o = ~i; }
void dpii_v_byte (char i, char *o)			{ *o = ~i; }
void dpii_v_shortint (short int i, short int *o)	{ *o = ~i; }
void dpii_v_ushort (unsigned short i, unsigned short *o) { *o = ~i; }
void dpii_v_longint (long long i, long long *o)		{ *o = ~i; }
void dpii_v_ulong (unsigned long long i, unsigned long long *o)	{ *o = ~i; }
void dpii_v_chandle (void* i, void* *o)			{ *o = i; }
void dpii_v_string   (const char* i, const char** o)	{ *o = i; }
void dpii_v_real     (double i,      double* o)		{ *o = i + 1.5; }
void dpii_v_shortreal(float i,       float* o)		{ *o = i + 1.5; }

void dpii_v_bit64(const svBitVecVal* i, svBitVecVal* o)	{
    o[0] = ~i[0];
    o[1] = ~i[1];
}
void dpii_v_bit95(const svBitVecVal* i, svBitVecVal* o)	{
    o[0] = ~i[0];
    o[1] = ~i[1];
    o[2] = SV_MASK(95-64) & ~i[2];
}
void dpii_v_bit96(const svBitVecVal* i, svBitVecVal* o)	{
    o[0] = ~i[0];
    o[1] = ~i[1];
    o[2] = ~i[2];
}

int  dpii_f_strlen (const char* i) { return strlen(i); }

//======================================================================

void dpii_f_void () {}

#ifdef VCS
void dpii_t_void () {}
void dpii_t_void_context () {}
void dpii_t_int (int i, int *o) {
    *o = i;
}
#else
int dpii_t_void () { return svIsDisabledState(); }
int dpii_t_void_context () { return svIsDisabledState(); }
int dpii_t_int (int i, int *o) {
    *o = i;
    return svIsDisabledState();  // Tasks generally need this
}
#endif

int dpii_fa_bit (int i) {
    return ~i;
}
