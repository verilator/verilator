// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: Linked against all applications using Verilated source.
///
///	This file must be compiled and linked against all objects
///	created from Verilator.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#define _VERILATED_CPP_
#include "verilated_imp.h"
#include <cctype>

#define VL_VALUE_STRING_MAX_WIDTH 8192	///< Max static char array for VL_VALUE_STRING

//===========================================================================
// Global variables

// Slow path variables
VerilatedVoidCb Verilated::s_flushCb = NULL;

// Keep below together in one cache line
Verilated::Serialized Verilated::s_s;
VL_THREAD const VerilatedScope* Verilated::t_dpiScopep = NULL;
VL_THREAD const char* Verilated::t_dpiFilename = "";
VL_THREAD int Verilated::t_dpiLineno = 0;
struct Verilated::CommandArgValues Verilated::s_args = {0, NULL};

VerilatedImp  VerilatedImp::s_s;

//===========================================================================
// User definable functions

#ifndef VL_USER_FINISH		// Define this to override this function
void vl_finish (const char* filename, int linenum, const char* hier) {
    if (0 && hier) {}
    VL_PRINTF("- %s:%d: Verilog $finish\n", filename, linenum);
    if (Verilated::gotFinish()) {
	VL_PRINTF("- %s:%d: Second verilog $finish, exiting\n", filename, linenum);
	Verilated::flushCall();
	exit(0);
    }
    Verilated::gotFinish(true);
}
#endif

#ifndef VL_USER_STOP		// Define this to override this function
void vl_stop (const char* filename, int linenum, const char* hier) {
    Verilated::gotFinish(true);
    Verilated::flushCall();
    vl_fatal (filename,linenum,hier,"Verilog $stop");
}
#endif

#ifndef VL_USER_FATAL	// Define this to override this function
void vl_fatal (const char* filename, int linenum, const char* hier, const char* msg) {
    if (0 && hier) {}
    Verilated::gotFinish(true);
    VL_PRINTF("%%Error: %s:%d: %s\n", filename, linenum, msg);
    Verilated::flushCall();

    VL_PRINTF("Aborting...\n");
    Verilated::flushCall();  // Second flush in case VL_PRINTF does something needing a flush
    abort();
}
#endif

//===========================================================================
// Overall class init

Verilated::Serialized::Serialized() {
    s_randReset = 0;
    s_debug = 0;
    s_calcUnusedSigs = false;
    s_gotFinish = false;
    s_assertOn = true;
    s_fatalOnVpiError = true; // retains old default behaviour
}

//===========================================================================
// Random reset -- Only called at init time, so don't inline.

IData VL_RAND32() {
#if defined(_WIN32) && !defined(__CYGWIN__)
    // Windows doesn't have lrand48(), although Cygwin does.
    return (rand()<<16) ^ rand();
#else
    return (lrand48()<<16) ^ lrand48();
#endif
}

IData VL_RANDOM_I(int obits) {
    return VL_RAND32() & VL_MASK_I(obits);
}

QData VL_RANDOM_Q(int obits) {
    QData data = ((QData)VL_RAND32()<<VL_ULL(32)) | (QData)VL_RAND32();
    return data & VL_MASK_Q(obits);
}

WDataOutP VL_RANDOM_W(int obits, WDataOutP outwp) {
    for (int i=0; i<VL_WORDS_I(obits); i++) {
	if (i<(VL_WORDS_I(obits)-1)) {
	    outwp[i] = VL_RAND32();
	} else {
	    outwp[i] = VL_RAND32() & VL_MASK_I(obits);
	}
    }
    return outwp;
}

IData VL_RAND_RESET_I(int obits) {
    if (Verilated::randReset()==0) return 0;
    IData data = ~0;
    if (Verilated::randReset()!=1) {	// if 2, randomize
	data = VL_RANDOM_I(obits);
    }
    if (obits<32) data &= VL_MASK_I(obits);
    return data;
}

QData VL_RAND_RESET_Q(int obits) {
    if (Verilated::randReset()==0) return 0;
    QData data = VL_ULL(~0);
    if (Verilated::randReset()!=1) {	// if 2, randomize
	data = VL_RANDOM_Q(obits);
    }
    if (obits<64) data &= VL_MASK_Q(obits);
    return data;
}

WDataOutP VL_RAND_RESET_W(int obits, WDataOutP outwp) {
    for (int i=0; i<VL_WORDS_I(obits); i++) {
	if (i<(VL_WORDS_I(obits)-1)) {
	    outwp[i] = VL_RAND_RESET_I(32);
	} else {
	    outwp[i] = VL_RAND_RESET_I(32) & VL_MASK_I(obits);
	}
    }
    return outwp;
}

WDataOutP VL_ZERO_RESET_W(int obits, WDataOutP outwp) {
    for (int i=0; i<VL_WORDS_I(obits); i++) outwp[i] = 0;
    return outwp;
}

//===========================================================================
// Debug

void _VL_DEBUG_PRINT_W(int lbits, WDataInP iwp) {
    VL_PRINTF("  Data: w%d: ", lbits);
    for (int i=VL_WORDS_I(lbits)-1; i>=0; i--) { VL_PRINTF("%08x ",iwp[i]); }
    VL_PRINTF("\n");
}

//===========================================================================
// Slow math

WDataOutP _vl_moddiv_w(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp, bool is_modulus) {
    // See Knuth Algorithm D.  Computes u/v = q.r
    // This isn't massively tuned, as wide division is rare
    // for debug see V3Number version
    // Requires clean input
    int words = VL_WORDS_I(lbits);
    for (int i=0; i<words; i++) owp[i]=0;
    // Find MSB and check for zero.
    int umsbp1 = VL_MOSTSETBITP1_W(words,lwp); // dividend
    int vmsbp1 = VL_MOSTSETBITP1_W(words,rwp); // divisor
    if (VL_UNLIKELY(vmsbp1==0)  // rwp==0 so division by zero.  Return 0.
	|| VL_UNLIKELY(umsbp1==0)) {	// 0/x so short circuit and return 0
	return owp;
    }

    int uw = VL_WORDS_I(umsbp1);  // aka "m" in the algorithm
    int vw = VL_WORDS_I(vmsbp1);  // aka "n" in the algorithm

    if (vw == 1) {  // Single divisor word breaks rest of algorithm
	vluint64_t k = 0;
	for (int j = uw-1; j >= 0; j--) {
	    vluint64_t unw64 = ((k<<VL_ULL(32)) + (vluint64_t)(lwp[j]));
	    owp[j] = unw64 / (vluint64_t)(rwp[0]);
	    k      = unw64 - (vluint64_t)(owp[j])*(vluint64_t)(rwp[0]);
	}
	if (is_modulus) {
	    owp[0] = k;
	    for (int i=1; i<words; i++) owp[i]=0;
	}
	return owp;
    }

    // +1 word as we may shift during normalization
    vluint32_t un[VL_MULS_MAX_WORDS+1]; // Fixed size, as MSVC++ doesn't allow [words] here
    vluint32_t vn[VL_MULS_MAX_WORDS+1]; // v normalized

    // Zero for ease of debugging and to save having to zero for shifts
    // Note +1 as loop will use extra word
    for (int i=0; i<words+1; i++) { un[i]=vn[i]=0; }

    // Algorithm requires divisor MSB to be set
    // Copy and shift to normalize divisor so MSB of vn[vw-1] is set
    int s = 31-VL_BITBIT_I(vmsbp1-1);  // shift amount (0...31)
    vluint32_t shift_mask = s ? 0xffffffff : 0;  // otherwise >> 32 won't mask the value
    for (int i = vw-1; i>0; i--) {
	vn[i] = (rwp[i] << s) | (shift_mask & (rwp[i-1] >> (32-s)));
    }
    vn[0] = rwp[0] << s;

    // Copy and shift dividend by same amount; may set new upper word
    if (s) un[uw] = lwp[uw-1] >> (32-s);
    else un[uw] = 0;
    for (int i=uw-1; i>0; i--) {
	un[i] = (lwp[i] << s) | (shift_mask & (lwp[i-1] >> (32-s)));
    }
    un[0] = lwp[0] << s;

    // Main loop
    for (int j = uw - vw; j >= 0; j--) {
	// Estimate
	vluint64_t unw64 = ((vluint64_t)(un[j+vw])<<VL_ULL(32) | (vluint64_t)(un[j+vw-1]));
	vluint64_t qhat = unw64 / (vluint64_t)(vn[vw-1]);
	vluint64_t rhat = unw64 - qhat*(vluint64_t)(vn[vw-1]);

      again:
	if (qhat >= VL_ULL(0x100000000)
	    || ((qhat*vn[vw-2]) > ((rhat<<VL_ULL(32)) + un[j+vw-2]))) {
	    qhat = qhat - 1;
	    rhat = rhat + vn[vw-1];
	    if (rhat < VL_ULL(0x100000000)) goto again;
	}

	vlsint64_t t = 0;  // Must be signed
	vluint64_t k = 0;
	for (int i=0; i<vw; i++) {
	    vluint64_t p = qhat*vn[i];  // Multiply by estimate
	    t = un[i+j] - k - (p & VL_ULL(0xFFFFFFFF));  // Subtract
	    un[i+j] = t;
	    k = (p >> VL_ULL(32)) - (t >> VL_ULL(32));
	}
	t = un[j+vw] - k;
	un[j+vw] = t;
	owp[j] = qhat; // Save quotient digit

	if (t < 0) {
	    // Over subtracted; correct by adding back
	    owp[j]--;
	    k = 0;
	    for (int i=0; i<vw; i++) {
		t = (vluint64_t)(un[i+j]) + (vluint64_t)(vn[i]) + k;
		un[i+j] = t;
		k = t >> VL_ULL(32);
	    }
	    un[j+vw] = un[j+vw] + k;
	}
    }

    if (is_modulus) { // modulus
	// Need to reverse normalization on copy to output
	for (int i=0; i<vw; i++) {
	    owp[i] = (un[i] >> s) | (shift_mask & (un[i+1] << (32-s)));
	}
	for (int i=vw; i<words; i++) owp[i] = 0;
	return owp;
    } else { // division
	return owp;
    }
}

//===========================================================================
// Formatting

// Do a va_arg returning a quad, assuming input argument is anything less than wide
#define _VL_VA_ARG_Q(ap, bits) (((bits) <= VL_WORDSIZE) ? va_arg(ap,IData) : va_arg(ap,QData))

void _vl_vsformat(string& output, const char* formatp, va_list ap) {
    // Format a Verilog $write style format into the output list
    // The format must be pre-processed (and lower cased) by Verilator
    // Arguments are in "width, arg-value (or WDataIn* if wide)" form
    //
    // Note uses a single buffer internally; presumes only one usage per printf
    // Note also assumes variables < 64 are not wide, this assumption is
    // sometimes not true in low-level routines written here in verilated.cpp
    static VL_THREAD char tmp[VL_VALUE_STRING_MAX_WIDTH];
    static VL_THREAD char tmpf[VL_VALUE_STRING_MAX_WIDTH];
    const char* pctp = NULL;  // Most recent %##.##g format
    bool inPct = false;
    bool widthSet = false;
    int width = 0;
    const char* pos = formatp;
    for (; *pos; ++pos) {
	if (!inPct && pos[0]=='%') {
	    pctp = pos;
	    inPct = true;
	    widthSet = false;
	    width = 0;
	} else if (!inPct) {   // Normal text
	    // Fast-forward to next escape and add to output
	    const char *ep = pos;
	    while (ep[0] && ep[0]!='%') ep++;
	    if (ep != pos) {
		output.append(pos, ep-pos);
		pos += ep-pos-1;
	    }
	} else { // Format character
	    inPct = false;
	    char fmt = pos[0];
	    switch (fmt) {
	    case '0': case '1': case '2': case '3': case '4':
	    case '5': case '6': case '7': case '8': case '9':
		inPct = true;  // Get more digits
		widthSet = true;
		width = width*10 + (fmt - '0');
		break;
	    case '.':
		inPct = true;  // Get more digits
		break;
	    case '%':
		output += '%';
		break;
	    case 'N': { // "C" string with name of module, add . if needed
		const char* cstrp = va_arg(ap, const char*);
		if (VL_LIKELY(*cstrp)) { output += cstrp; output += '.'; }
		break;
	    }
	    case 'S': { // "C" string
		const char* cstrp = va_arg(ap, const char*);
		output += cstrp;
		break;
	    }
	    case '@': { // Verilog/C++ string
		va_arg(ap, int);  // # bits is ignored
		const string* cstrp = va_arg(ap, const string*);
		output += *cstrp;
		break;
	    }
	    case 'e':
	    case 'f':
	    case 'g': {
		const int lbits = va_arg(ap, int);
		double d = va_arg(ap, double);
		if (lbits) {}  // UNUSED - always 64
		strncpy(tmpf, pctp, pos-pctp+1);
		tmpf[pos-pctp+1] = '\0';
		sprintf(tmp, tmpf, d);
		output += tmp;
		break;
	    }
	    default: {
		// Deal with all read-and-print somethings
		const int lbits = va_arg(ap, int);
		QData ld = 0;
		WData qlwp[2];
		WDataInP lwp;
		if (lbits <= VL_QUADSIZE) {
		    ld = _VL_VA_ARG_Q(ap, lbits);
		    VL_SET_WQ(qlwp,ld);
		    lwp = qlwp;
		} else {
		    lwp = va_arg(ap,WDataInP);
		    ld = lwp[0];
		    if (fmt == 'u' || fmt == 'd') fmt = 'x';  // Not supported, but show something
		}
		int lsb=lbits-1;
		if (widthSet && width==0) while (lsb && !VL_BITISSET_W(lwp,lsb)) lsb--;
		switch (fmt) {
		case 'c': {
		    IData charval = ld & 0xff;
		    output += charval;
		    break;
		}
		case 's':
		    for (; lsb>=0; lsb--) {
			lsb = (lsb / 8) * 8; // Next digit
			IData charval = (lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xff;
			output += (charval==0)?' ':charval;
		    }
		    break;
		case 'd': { // Signed decimal
		    int digits=sprintf(tmp,"%" VL_PRI64 "d",(vlsint64_t)(VL_EXTENDS_QQ(lbits,lbits,ld)));
		    int needmore = width-digits;
		    if (needmore>0) {
			if (pctp && pctp[0] && pctp[1]=='0') { //%0
			    output.append(needmore,'0'); // Pre-pad zero
			} else {
			    output.append(needmore,' '); // Pre-pad spaces
			}
		    }
		    output += tmp;
		    break;
		}
		case 'u': { // Unsigned decimal
		    int digits=sprintf(tmp,"%" VL_PRI64 "u",ld);
		    int needmore = width-digits;
		    if (needmore>0) {
			if (pctp && pctp[0] && pctp[1]=='0') { //%0
			    output.append(needmore,'0'); // Pre-pad zero
			} else {
			    output.append(needmore,' '); // Pre-pad spaces
			}
		    }
		    output += tmp;
		    break;
		}
		case 't': { // Time
		    int digits;
		    if (VL_TIME_MULTIPLIER==1) {
			digits=sprintf(tmp,"%" VL_PRI64 "u",ld);
		    } else if (VL_TIME_MULTIPLIER==1000) {
			digits=sprintf(tmp,"%" VL_PRI64 "u.%03" VL_PRI64 "u",
				       (QData)(ld/VL_TIME_MULTIPLIER),
				       (QData)(ld%VL_TIME_MULTIPLIER));
		    } else {
			vl_fatal(__FILE__,__LINE__,"","Unsupported VL_TIME_MULTIPLIER");
		    }
		    int needmore = width-digits;
		    if (needmore>0) output.append(needmore,' '); // Pre-pad spaces
		    output += tmp;
		    break;
		}
		case 'b':
		    for (; lsb>=0; lsb--) {
			output += ((lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 1) + '0';
		    }
		    break;
		case 'o':
		    for (; lsb>=0; lsb--) {
			lsb = (lsb / 3) * 3; // Next digit
			// Octal numbers may span more than one wide word,
			// so we need to grab each bit separately and check for overrun
			// Octal is rare, so we'll do it a slow simple way
			output += ('0'
				   + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb+0)) ? 1 : 0)
				   + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb+1)) ? 2 : 0)
				   + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb+2)) ? 4 : 0));
		    }
		    break;
		case 'x':
		    for (; lsb>=0; lsb--) {
			lsb = (lsb / 4) * 4; // Next digit
			IData charval = (lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xf;
			output += "0123456789abcdef"[charval];
		    }
		    break;
		default:
		    string msg = string("Unknown _vl_vsformat code: ")+pos[0];
		    vl_fatal(__FILE__,__LINE__,"",msg.c_str());
		    break;
		} // switch
	    }
	    } // switch
	}
    }
}

static inline bool _vl_vsss_eof(FILE* fp, int& floc) {
    if (fp) return feof(fp) ? 1 : 0;  // 1:0 to prevent MSVC++ warning
    else return (floc<0);
}
static inline void _vl_vsss_advance(FILE* fp, int& floc) {
    if (fp) fgetc(fp);
    else floc -= 8;
}
static inline int  _vl_vsss_peek(FILE* fp, int& floc, WDataInP fromp, const string& fstr) {
    // Get a character without advancing
    if (fp) {
	int data = fgetc(fp);
	if (data == EOF) return EOF;
	ungetc(data,fp);
	return data;
    } else {
	if (floc < 0) return EOF;
	floc = floc & ~7;	// Align to closest character
	if (fromp == NULL) {
	    return fstr[fstr.length()-1 - (floc>>3)];
	} else {
	    return (fromp[VL_BITWORD_I(floc)] >> VL_BITBIT_I(floc)) & 0xff;
	}
    }
}
static inline void _vl_vsss_skipspace(FILE* fp, int& floc, WDataInP fromp, const string& fstr) {
    while (1) {
	int c = _vl_vsss_peek(fp, floc, fromp, fstr);
	if (c==EOF || !isspace(c)) return;
	_vl_vsss_advance(fp, floc);
    }
}
static inline void _vl_vsss_read(FILE* fp, int& floc, WDataInP fromp, const string& fstr,
				 char* tmpp, const char* acceptp) {
    // Read into tmp, consisting of characters from acceptp list
    char* cp = tmpp;
    while (1) {
	int c = _vl_vsss_peek(fp, floc, fromp, fstr);
	if (c==EOF || isspace(c)) break;
	if (acceptp!=NULL // String - allow anything
	    && NULL==strchr(acceptp, c)) break;
	if (acceptp!=NULL) c = tolower(c); // Non-strings we'll simplify
	*cp++ = c;
	_vl_vsss_advance(fp, floc);
    }
    *cp++ = '\0';
    //VL_PRINTF("\t_read got='%s'\n", tmpp);
}
static inline void _vl_vsss_setbit(WDataOutP owp, int obits, int lsb, int nbits, IData ld) {
    for (; nbits && lsb<obits; nbits--, lsb++, ld>>=1) {
	VL_ASSIGNBIT_WI(0, lsb, owp, ld & 1);
    }
}
static inline void _vl_vsss_based(WDataOutP owp, int obits, int baseLog2, const char* strp, int posstart, int posend) {
    // Read in base "2^^baseLog2" digits from strp[posstart..posend-1] into owp of size obits.
    int lsb = 0;
    for (int i=0, pos=posend-1; i<obits && pos>=posstart; pos--) {
	switch (tolower (strp[pos])) {
	case 'x': case 'z': case '?': //FALLTHRU
	case '0': lsb += baseLog2; break;
	case '1': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  1); lsb+=baseLog2; break;
	case '2': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  2); lsb+=baseLog2; break;
	case '3': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  3); lsb+=baseLog2; break;
	case '4': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  4); lsb+=baseLog2; break;
	case '5': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  5); lsb+=baseLog2; break;
	case '6': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  6); lsb+=baseLog2; break;
	case '7': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  7); lsb+=baseLog2; break;
	case '8': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  8); lsb+=baseLog2; break;
	case '9': _vl_vsss_setbit(owp,obits,lsb, baseLog2,  9); lsb+=baseLog2; break;
	case 'a': _vl_vsss_setbit(owp,obits,lsb, baseLog2, 10); lsb+=baseLog2; break;
	case 'b': _vl_vsss_setbit(owp,obits,lsb, baseLog2, 11); lsb+=baseLog2; break;
	case 'c': _vl_vsss_setbit(owp,obits,lsb, baseLog2, 12); lsb+=baseLog2; break;
	case 'd': _vl_vsss_setbit(owp,obits,lsb, baseLog2, 13); lsb+=baseLog2; break;
	case 'e': _vl_vsss_setbit(owp,obits,lsb, baseLog2, 14); lsb+=baseLog2; break;
	case 'f': _vl_vsss_setbit(owp,obits,lsb, baseLog2, 15); lsb+=baseLog2; break;
	case '_': break;
	}
    }
}

IData _vl_vsscanf(FILE* fp,  // If a fscanf
		  int fbits, WDataInP fromp,  // Else if a sscanf
		  const string& fstr,  // if a sscanf to string
		  const char* formatp, va_list ap) {
    // Read a Verilog $sscanf/$fscanf style format into the output list
    // The format must be pre-processed (and lower cased) by Verilator
    // Arguments are in "width, arg-value (or WDataIn* if wide)" form
    static VL_THREAD char tmp[VL_VALUE_STRING_MAX_WIDTH];
    int floc = fbits - 1;
    IData got = 0;
    bool inPct = false;
    const char* pos = formatp;
    for (; *pos && !_vl_vsss_eof(fp,floc); ++pos) {
	//VL_PRINTF("_vlscan fmt='%c' floc=%d file='%c'\n", pos[0], floc, _vl_vsss_peek(fp,floc,fromp,fstr));
	if (!inPct && pos[0]=='%') {
	    inPct = true;
	} else if (!inPct && isspace(pos[0])) {   // Format spaces
	    while (isspace(pos[1])) pos++;
	    _vl_vsss_skipspace(fp,floc,fromp,fstr);
	} else if (!inPct) {   // Expected Format
	    _vl_vsss_skipspace(fp,floc,fromp,fstr);
	    int c = _vl_vsss_peek(fp,floc,fromp,fstr);
	    if (c != pos[0]) goto done;
	    else _vl_vsss_advance(fp,floc);
	} else { // Format character
	    // Skip loading spaces
	    inPct = false;
	    char fmt = pos[0];
	    switch (fmt) {
	    case '%': {
		int c = _vl_vsss_peek(fp,floc,fromp,fstr);
		if (c != '%') goto done;
		else _vl_vsss_advance(fp,floc);
		break;
	    }
	    default: {
		// Deal with all read-and-scan somethings
		// Note LSBs are preserved if there's an overflow
		const int obits = va_arg(ap, int);
		WData qowp[2];
		WDataOutP owp = qowp;
		if (obits > VL_QUADSIZE) {
		    owp = va_arg(ap,WDataOutP);
		}
		for (int i=0; i<VL_WORDS_I(obits); i++) owp[i] = 0;
		switch (fmt) {
		case 'c': {
		    int c = _vl_vsss_peek(fp,floc,fromp,fstr);
		    if (c==EOF) goto done;
		    else _vl_vsss_advance(fp,floc);
		    owp[0] = c;
		    break;
		}
		case 's': {
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, NULL);
		    if (!tmp[0]) goto done;
		    int pos = ((int)strlen(tmp))-1;
		    int lsb = 0;
		    for (int i=0; i<obits && pos>=0; pos--) {
			_vl_vsss_setbit(owp,obits,lsb, 8, tmp[pos]); lsb+=8;
		    }
		    break;
		}
		case 'd': { // Signed decimal
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, "0123456789+-xXzZ?_");
		    if (!tmp[0]) goto done;
		    vlsint64_t ld;
		    sscanf(tmp,"%30" VL_PRI64 "d",&ld);
		    VL_SET_WQ(owp,ld);
		    break;
		}
		case 'f':
		case 'e':
		case 'g': { // Real number
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, "+-.0123456789eE");
		    if (!tmp[0]) goto done;
		    union { double r; vlsint64_t ld; } u;
		    u.r = strtod(tmp, NULL);
		    VL_SET_WQ(owp,u.ld);
		    break;
		}
		case 't': // FALLTHRU  // Time
		case 'u': { // Unsigned decimal
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, "0123456789+-xXzZ?_");
		    if (!tmp[0]) goto done;
		    QData ld;
		    sscanf(tmp,"%30" VL_PRI64 "u",&ld);
		    VL_SET_WQ(owp,ld);
		    break;
		}
		case 'b': {
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, "01xXzZ?_");
		    if (!tmp[0]) goto done;
		    _vl_vsss_based(owp,obits, 1, tmp, 0, (int)strlen(tmp));
		    break;
		}
		case 'o': {
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, "01234567xXzZ?_");
		    if (!tmp[0]) goto done;
		    _vl_vsss_based(owp,obits, 3, tmp, 0, (int)strlen(tmp));
		    break;
		}
		case 'x': {
		    _vl_vsss_skipspace(fp,floc,fromp,fstr);
		    _vl_vsss_read(fp,floc,fromp,fstr, tmp, "0123456789abcdefABCDEFxXzZ?_");
		    if (!tmp[0]) goto done;
		    _vl_vsss_based(owp,obits, 4, tmp, 0, (int)strlen(tmp));
		    break;
		}
		default:
		    string msg = string("Unknown _vl_vsscanf code: ")+pos[0];
		    vl_fatal(__FILE__,__LINE__,"",msg.c_str());
		    break;
		} // switch

		got++;
		// Reload data if non-wide (if wide, we put it in the right place directly)
		if (obits <= VL_BYTESIZE) {
		    CData* p = va_arg(ap,CData*); *p = owp[0];
		} else if (obits <= VL_SHORTSIZE) {
		    SData* p = va_arg(ap,SData*); *p = owp[0];
		} else if (obits <= VL_WORDSIZE) {
		    IData* p = va_arg(ap,IData*); *p = owp[0];
		} else if (obits <= VL_QUADSIZE) {
		    QData* p = va_arg(ap,QData*); *p = VL_SET_QW(owp);
		}
	    }
	    } // switch
	}
    }
  done:
    return got;
}

//===========================================================================
// File I/O

FILE* VL_CVT_I_FP(IData lhs) {
    return VerilatedImp::fdToFp(lhs);
}

void _VL_VINT_TO_STRING(int obits, char* destoutp, WDataInP sourcep) {
    // See also VL_DATA_TO_STRING_NW
    int lsb=obits-1;
    bool start=true;
    char* destp = destoutp;
    for (; lsb>=0; lsb--) {
	lsb = (lsb / 8) * 8; // Next digit
	IData charval = (sourcep[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xff;
	if (!start || charval) {
	    *destp++ = (charval==0)?' ':charval;
	    start = false;	// Drop leading 0s
	}
    }
    *destp = '\0'; // Terminate
    if (!start) while (isspace(*(destp-1)) && destp>destoutp) *--destp = '\0';  // Drop trailing spaces
}

void _VL_STRING_TO_VINT(int obits, void* destp, int srclen, const char* srcp) {
    // Convert C string to Verilog format
    int bytes = VL_BYTES_I(obits);
    char* op = ((char*)(destp));
    if (srclen > bytes) srclen = bytes;  // Don't overflow destination
    int i;
    for (i=0; i<srclen; i++) { *op++ = srcp[srclen-1-i]; }
    for (; i<bytes; i++) { *op++ = 0; }
}

IData VL_FGETS_IXI(int obits, void* destp, IData fpi) {
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;

    // The string needs to be padded with 0's in unused spaces in front of
    // any read data.  This means we can't know in what location the first
    // character will finally live, so we need to copy.  Yuk.
    IData bytes = VL_BYTES_I(obits);
    char buffer[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    // V3Emit has static check that bytes < VL_TO_STRING_MAX_WORDS, but be safe
    if (VL_UNLIKELY(bytes > VL_TO_STRING_MAX_WORDS*VL_WORDSIZE)) {
	vl_fatal(__FILE__,__LINE__,"","Internal: fgets buffer overrun");
    }

    // We don't use fgets, as we must read \0s.
    IData got = 0;
    char* cp = buffer;
    while (got < bytes) {
	int c = getc(fp);
	if (c==EOF) break;
	*cp++ = c;  got++;
	if (c=='\n') break;
    }

    _VL_STRING_TO_VINT(obits, destp, got, buffer);
    return got;
}

IData VL_FOPEN_NI(const string& filename, IData mode) {
    char modez[5];
    _VL_VINT_TO_STRING(VL_WORDSIZE, modez, &mode);
    return VL_FOPEN_S(filename.c_str(), modez);
}
IData VL_FOPEN_QI(QData filename, IData mode) {
    IData fnw[2];  VL_SET_WQ(fnw, filename);
    return VL_FOPEN_WI(2, fnw, mode);
}
IData VL_FOPEN_WI(int fnwords, WDataInP filenamep, IData mode) {
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(fnwords*VL_WORDSIZE, filenamez, filenamep);
    char modez[5];
    _VL_VINT_TO_STRING(VL_WORDSIZE, modez, &mode);
    return VL_FOPEN_S(filenamez,modez);
}
IData VL_FOPEN_S(const char* filenamep, const char* modep) {
    return VerilatedImp::fdNew(fopen(filenamep,modep));
}

void VL_FCLOSE_I(IData fdi) {
    FILE* fp = VL_CVT_I_FP(fdi);
    if (VL_UNLIKELY(!fp)) return;
    fclose(fp);
    VerilatedImp::fdDelete(fdi);
}

void VL_SFORMAT_X(int obits, CData& destr, const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, (int)output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, SData& destr, const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, (int)output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, IData& destr, const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, (int)output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, QData& destr, const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, (int)output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, void* destp, const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, destp, (int)output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits_ignored, string &output, const char* formatp, ...) {
    if (obits_ignored) {}
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);
}

string VL_SFORMATF_NX(const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    return output;
}

void VL_WRITEF(const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    // Users can redefine VL_PRINTF if they wish.
    VL_PRINTF("%s", output.c_str());
}

void VL_FWRITEF(IData fpi, const char* formatp, ...) {
    VL_STATIC_OR_THREAD string output;  // static only for speed
    output = "";
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return;

    va_list ap;
    va_start(ap,formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    fputs(output.c_str(), fp);
}

IData VL_FSCANF_IX(IData fpi, const char* formatp, ...) {
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;

    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(fp, 0, NULL, "", formatp, ap);
    va_end(ap);
    return got;
}

IData VL_SSCANF_IIX(int lbits, IData ld, const char* formatp, ...) {
    IData fnw[2];  VL_SET_WI(fnw, ld);

    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IQX(int lbits, QData ld, const char* formatp, ...) {
    IData fnw[2];  VL_SET_WQ(fnw, ld);

    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IWX(int lbits, WDataInP lwp, const char* formatp, ...) {
    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, lbits, lwp, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_INX(int, const string& ld, const char* formatp, ...) {
    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, ld.length()*8, NULL, ld, formatp, ap);
    va_end(ap);
    return got;
}

void VL_READMEM_Q(bool hex, int width, int depth, int array_lsb, int,
		  QData ofilename, void* memp, IData start, IData end) {
    IData fnw[2];  VL_SET_WQ(fnw, ofilename);
    return VL_READMEM_W(hex,width,depth,array_lsb,2, fnw,memp,start,end);
}

void VL_READMEM_W(bool hex, int width, int depth, int array_lsb, int fnwords,
		  WDataInP ofilenamep, void* memp, IData start, IData end) {
    char ofilenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(fnwords*VL_WORDSIZE, ofilenamez, ofilenamep);
    FILE* fp = fopen(ofilenamez, "r");
    if (VL_UNLIKELY(!fp)) {
	// We don't report the Verilog source filename as it slow to have to pass it down
	vl_fatal (ofilenamez, 0, "", "$readmem file not found");
	return;
    }
    // Prep for reading
    IData addr = start;
    int linenum = 1;
    bool innum = false;
    bool ignore_to_eol = false;
    bool ignore_to_cmt = false;
    bool needinc = false;
    bool reading_addr = false;
    int lastc = ' ';
    // Read the data
    // We process a character at a time, as then we don't need to deal
    // with changing buffer sizes dynamically, etc.
    while (1) {
	int c = fgetc(fp);
	if (VL_UNLIKELY(c==EOF)) break;
	//printf("%d: Got '%c' Addr%x IN%d IgE%d IgC%d ninc%d\n", linenum, c, addr, innum, ignore_to_eol, ignore_to_cmt, needinc);
	if (c=='\n') { linenum++; ignore_to_eol=false; if (innum) reading_addr=false; innum=false; }
	else if (c=='\t' || c==' ' || c=='\r' || c=='\f') { if (innum) reading_addr=false; innum=false; }
	// Skip // comments and detect /* comments
	else if (ignore_to_cmt && lastc=='*' && c=='/') {
	    ignore_to_cmt = false; if (innum) reading_addr=false; innum=false;
	} else if (!ignore_to_eol && !ignore_to_cmt) {
	    if (lastc=='/' && c=='*') { ignore_to_cmt = true; }
	    else if (lastc=='/' && c=='/') { ignore_to_eol = true; }
	    else if (c=='/') {}  // Part of /* or //
	    else if (c=='_') {}
	    else if (c=='@') { reading_addr = true; innum=false; needinc=false; }
	    // Check for hex or binary digits as file format requests
	    else if (isxdigit(c)) {
		c = tolower(c);
		int value = (c >= 'a' ? (c-'a'+10) : (c-'0'));
		if (!innum) {  // Prep for next number
		    if (needinc) { addr++; needinc=false; }
		}
		if (reading_addr) {
		    // Decode @ addresses
		    if (!innum) addr=0;
		    addr = (addr<<4) + value;
		} else {
		    needinc = true;
		    //printf(" Value width=%d  @%x = %c\n", width, addr, c);
		    if (VL_UNLIKELY(addr >= (IData)(depth+array_lsb) || addr < (IData)(array_lsb))) {
			vl_fatal (ofilenamez, linenum, "", "$readmem file address beyond bounds of array");
		    } else {
			int entry = addr - array_lsb;
			QData shift = hex ? VL_ULL(4) : VL_ULL(1);
			// Shift value in
			if (width<=8) {
			    CData* datap = &((CData*)(memp))[entry];
			    if (!innum) { *datap = 0; }
			    *datap = ((*datap << shift) + value) & VL_MASK_I(width);
			} else if (width<=16) {
			    SData* datap = &((SData*)(memp))[entry];
			    if (!innum) { *datap = 0; }
			    *datap = ((*datap << shift) + value) & VL_MASK_I(width);
			} else if (width<=VL_WORDSIZE) {
			    IData* datap = &((IData*)(memp))[entry];
			    if (!innum) { *datap = 0; }
			    *datap = ((*datap << shift) + value) & VL_MASK_I(width);
			} else if (width<=VL_QUADSIZE) {
			    QData* datap = &((QData*)(memp))[entry];
			    if (!innum) { *datap = 0; }
			    *datap = ((*datap << (QData)(shift)) + (QData)(value)) & VL_MASK_Q(width);
			} else {
			    WDataOutP datap = &((WDataOutP)(memp))[ entry*VL_WORDS_I(width) ];
			    if (!innum) { VL_ZERO_RESET_W(width, datap); }
			    _VL_SHIFTL_INPLACE_W(width, datap, (IData)shift);
			    datap[0] |= value;
			}
			if (VL_UNLIKELY(value>=(1<<shift))) {
			    vl_fatal (ofilenamez, linenum, "", "$readmemb (binary) file contains hex characters");
			}
		    }
		}
		innum = true;
	    }
	    else {
		vl_fatal (ofilenamez, linenum, "", "$readmem file syntax error");
	    }
	}
	lastc = c;
    }
    if (needinc) { addr++; needinc=false; }

    // Final checks
    fclose(fp);
    if (VL_UNLIKELY(end != VL_UL(0xffffffff) && addr != (end+1))) {
	vl_fatal (ofilenamez, linenum, "", "$readmem file ended before specified ending-address");
    }
}

IData VL_SYSTEM_IQ(QData lhs) {
    IData lhsw[2];  VL_SET_WQ(lhsw, lhs);
    return VL_SYSTEM_IW(2, lhsw);
}
IData VL_SYSTEM_IW(int lhswords, WDataInP filenamep) {
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(lhswords*VL_WORDSIZE, filenamez, filenamep);
    int code = system(filenamez);
    return code >> 8;  // Want exit status
}

IData VL_TESTPLUSARGS_I(const char* formatp) {
    const string& match = VerilatedImp::argPlusMatch(formatp);
    if (match == "") return 0;
    else return 1;
}

IData VL_VALUEPLUSARGS_IW(int rbits, const char* prefixp, char fmt, WDataOutP rwp) {
    const string& match = VerilatedImp::argPlusMatch(prefixp);
    const char* dp = match.c_str() + 1 /*leading + */ + strlen(prefixp);
    if (match == "") return 0;
    VL_ZERO_RESET_W(rbits, rwp);
    switch (tolower(fmt)) {
    case '%':
	break;
    case 'd':
	vlsint64_t ld;
	sscanf(dp,"%30" VL_PRI64 "d",&ld);
	VL_SET_WQ(rwp,ld);
	break;
    case 'b':
	_vl_vsss_based(rwp,rbits, 1, dp, 0, (int)strlen(dp));
	break;
    case 'o':
	_vl_vsss_based(rwp,rbits, 3, dp, 0, (int)strlen(dp));
	break;
    case 'h': //FALLTHRU
    case 'x':
	_vl_vsss_based(rwp,rbits, 4, dp, 0, (int)strlen(dp));
	break;
    case 's':
	for (int i=0, lsb=0, pos=((int)strlen(dp))-1; i<rbits && pos>=0; pos--) {
	    _vl_vsss_setbit(rwp,rbits,lsb, 8, dp[pos]); lsb+=8;
	}
	break;
    default:  // Compile time should have found all errors before this
	vl_fatal (__FILE__, __LINE__, "", "$value$plusargs format error");
	break;
    }
    _VL_CLEAN_INPLACE_W(rbits,rwp);
    return 1;
}

const char* vl_mc_scan_plusargs(const char* prefixp) {
    const string& match = VerilatedImp::argPlusMatch(prefixp);
    static VL_THREAD char outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match == "") return NULL;
    strncpy(outstr, match.c_str()+strlen(prefixp)+1, // +1 to skip the "+"
	    VL_VALUE_STRING_MAX_WIDTH);
    outstr[VL_VALUE_STRING_MAX_WIDTH-1] = '\0';
    return outstr;
}

//===========================================================================
// Heavy functions

string VL_CVT_PACK_STR_NW(int lwords, WDataInP lwp) {
    // See also _VL_VINT_TO_STRING
    char destout[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    int obits = lwords * VL_WORDSIZE;
    int lsb=obits-1;
    bool start=true;
    char* destp = destout;
    int len = 0;
    for (; lsb>=0; lsb--) {
	lsb = (lsb / 8) * 8; // Next digit
	IData charval = (lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xff;
	if (!start || charval) {
	    *destp++ = (charval==0)?' ':charval;
	    len++;
	    start = false;	// Drop leading 0s
	}
    }
    return string(destout, len);
}

//===========================================================================
// Verilated:: Methods

const char* Verilated::catName(const char* n1, const char* n2) {
    // Returns new'ed data
    // Used by symbol table creation to make module names
    static char* strp = NULL;
    static size_t len  = 0;
    size_t newlen = strlen(n1)+strlen(n2)+2;
    if (newlen > len) {
	if (strp) delete [] strp;
	strp = new char[newlen];
	len = newlen;
    }
    strcpy(strp,n1);
    if (*n1) strcat(strp,".");
    strcat(strp,n2);
    return strp;
}

void Verilated::flushCb(VerilatedVoidCb cb) {
    if (s_flushCb == cb) {}  // Ok - don't duplicate
    else if (!s_flushCb) { s_flushCb=cb; }
    else {
	// Someday we may allow multiple callbacks ala atexit(), but until then
	vl_fatal("unknown",0,"", "Verilated::flushCb called twice with different callbacks");
    }
}

void Verilated::commandArgs(int argc, const char** argv) {
    s_args.argc = argc;
    s_args.argv = argv;
    VerilatedImp::commandArgs(argc,argv);
}

const char* Verilated::commandArgsPlusMatch(const char* prefixp) {
    return VerilatedImp::argPlusMatch(prefixp).c_str();
}

void Verilated::internalsDump() {
    VerilatedImp::internalsDump();
}

void Verilated::scopesDump() {
    VerilatedImp::scopesDump();
}

const VerilatedScope* Verilated::scopeFind(const char* namep) {
    return VerilatedImp::scopeFind(namep);
}

int Verilated::exportFuncNum(const char* namep) {
    return VerilatedImp::exportFind(namep);
}

//===========================================================================
// VerilatedModule:: Methods

VerilatedModule::VerilatedModule(const char* namep)
    : m_namep(strdup(namep)) {
}

VerilatedModule::~VerilatedModule() {
    if (m_namep) free((void*)m_namep); m_namep=NULL;
}

//======================================================================
// VerilatedVar:: Methods

// cppcheck-suppress unusedFunction  // Used by applications
vluint32_t VerilatedVar::entSize() const {
    vluint32_t size = 1;
    switch (vltype()) {
    case VLVT_PTR:	size=sizeof(void*); break;
    case VLVT_UINT8:	size=sizeof(CData); break;
    case VLVT_UINT16:	size=sizeof(SData); break;
    case VLVT_UINT32:	size=sizeof(IData); break;
    case VLVT_UINT64:	size=sizeof(QData); break;
    case VLVT_WDATA:	size=VL_WORDS_I(range().elements())*sizeof(IData); break;
    default:		size=0; break;
    }
    return size;
}

//======================================================================
// VerilatedScope:: Methods

VerilatedScope::VerilatedScope() {
    m_callbacksp = NULL;
    m_namep = NULL;
    m_funcnumMax = 0;
    m_symsp = NULL;
    m_varsp = NULL;
}

VerilatedScope::~VerilatedScope() {
    VerilatedImp::scopeErase(this);
    if (m_namep) { delete [] m_namep; m_namep = NULL; }
    if (m_callbacksp) { delete [] m_callbacksp; m_callbacksp = NULL; }
    if (m_varsp) { delete m_varsp; m_varsp = NULL; }
    m_funcnumMax = 0;  // Force callback table to empty
}

void VerilatedScope::configure(VerilatedSyms* symsp, const char* prefixp, const char* suffixp) {
    // Slowpath - called once/scope at construction
    // We don't want the space and reference-count access overhead of strings.
    m_symsp = symsp;
    char* namep = new char[strlen(prefixp)+strlen(suffixp)+2];
    strcpy(namep, prefixp);
    if (*prefixp && *suffixp) strcat(namep,".");
    strcat(namep, suffixp);
    m_namep = namep;
    VerilatedImp::scopeInsert(this);
}

void VerilatedScope::exportInsert(int finalize, const char* namep, void* cb) {
    // Slowpath - called once/scope*export at construction
    // Insert a exported function into scope table
    int funcnum = VerilatedImp::exportInsert(namep);
    if (!finalize) {
	// Need two passes so we know array size to create
	// Alternative is to dynamically stretch the array, which is more code, and slower.
	if (funcnum >= m_funcnumMax) { m_funcnumMax = funcnum+1; }
    } else {
	if (VL_UNLIKELY(funcnum >= m_funcnumMax)) {
	    vl_fatal(__FILE__,__LINE__,"","Internal: Bad funcnum vs. pre-finalize maximum");
	}
	if (VL_UNLIKELY(!m_callbacksp)) { // First allocation
	    m_callbacksp = new void* [m_funcnumMax];
	    memset(m_callbacksp, 0, m_funcnumMax*sizeof(void*));
	}
	m_callbacksp[funcnum] = cb;
    }
}

void VerilatedScope::varInsert(int finalize, const char* namep, void* datap,
			       VerilatedVarType vltype, int vlflags, int dims, ...) {
    // Grab dimensions
    // In the future we may just create a large table at emit time and statically construct from that.
    if (!finalize) return;

    if (!m_varsp) m_varsp = new VerilatedVarNameMap();
    VerilatedVar var (namep, datap, vltype, (VerilatedVarFlags)vlflags, dims);

    va_list ap;
    va_start(ap,dims);
    for (int i=0; i<dims; ++i) {
	int msb = va_arg(ap,int);
	int lsb = va_arg(ap,int);
	if (i==0) {
	    var.m_range.m_left = msb;
	    var.m_range.m_right = lsb;
	} else if (i==1) {
	    var.m_array.m_left = msb;
	    var.m_array.m_right = lsb;
	} else {
	    // We could have a linked list of ranges, but really this whole thing needs
	    // to be generalized to support structs and unions, etc.
	    vl_fatal(__FILE__,__LINE__,"",(string("Unsupported multi-dimensional public varInsert: ")+namep).c_str());
	}
    }
    va_end(ap);

    m_varsp->insert(make_pair(namep,var));
}

// cppcheck-suppress unusedFunction  // Used by applications
VerilatedVar* VerilatedScope::varFind(const char* namep) const {
    if (VL_LIKELY(m_varsp)) {
	VerilatedVarNameMap::iterator it = m_varsp->find(namep);
	if (VL_LIKELY(it != m_varsp->end())) {	
	    return &(it->second);
	}
    }
    return NULL;
}

void* VerilatedScope::exportFindNullError(int funcnum) const {
    // Slowpath - Called only when find has failed
    string msg = (string("Testbench C called '")
		  +VerilatedImp::exportName(funcnum)
		  +"' but scope wasn't set, perhaps due to dpi import call without 'context'");
    vl_fatal("unknown",0,"", msg.c_str());
    return NULL;
}

void* VerilatedScope::exportFindError(int funcnum) const {
    // Slowpath - Called only when find has failed
    string msg = (string("Testbench C called '")
		  +VerilatedImp::exportName(funcnum)
		  +"' but this DPI export function exists only in other scopes, not scope '"
		  +name()+"'");
    vl_fatal("unknown",0,"", msg.c_str());
    return NULL;
}

void VerilatedScope::scopeDump() const {
    VL_PRINTF("    SCOPE %p: %s\n", this, name());
    for (int i=0; i<m_funcnumMax; i++) {
	if (m_callbacksp && m_callbacksp[i]) {
	    VL_PRINTF("       DPI-EXPORT %p: %s\n",
		      m_callbacksp[i], VerilatedImp::exportName(i));
	}
    }
    if (VerilatedVarNameMap* varsp = this->varsp()) {
	for (VerilatedVarNameMap::const_iterator it = varsp->begin();
	     it != varsp->end(); ++it) {
	    VL_PRINTF("       VAR %p: %s\n", &(it->second), it->first);
	}
    }
}

//===========================================================================
