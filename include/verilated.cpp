// -*- C++ -*-
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License or the Perl Artistic License.
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

#include "verilated.h"
#include <cctype>

#define VL_VALUE_STRING_MAX_WIDTH 1024	///< Max static char array for VL_VALUE_STRING

//===========================================================================
// Global variables

int  Verilated::s_randReset = 0;
int  Verilated::s_debug = 1;
bool Verilated::s_calcUnusedSigs = false;
bool Verilated::s_gotFinish = false;
bool Verilated::s_assertOn = true;

//===========================================================================
// User definable functions

#ifndef VL_USER_FINISH		// Define this to override this function
void vl_finish (const char* filename, int linenum, const char* hier) {
    if (0 && hier) {}
    VL_PRINTF("- %s:%d: Verilog $finish\n", filename, linenum);
    if (Verilated::gotFinish()) {
	VL_PRINTF("- %s:%d: Second verilog $finish, exiting\n", filename, linenum);
	exit(0);
    }
    Verilated::gotFinish(true);
}
#endif

#ifndef VL_USER_STOP		// Define this to override this function
void vl_stop (const char* filename, int linenum, const char* hier) {
    Verilated::gotFinish(true);
    vl_fatal (filename,linenum,hier,"Verilog $stop");
}
#endif

#ifndef VL_USER_FATAL	// Define this to override this function
void vl_fatal (const char* filename, int linenum, const char* hier, const char* msg) {
    if (0 && hier) {}
    Verilated::gotFinish(true);
    VL_PRINTF("%%Error: %s:%d: %s\n", filename, linenum, msg);
    abort();
}
#endif

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
    bool inPct = false;
    bool widthSet = false;
    int width = 0;
    const char* pos = formatp;
    for (; *pos; ++pos) {
	if (!inPct && pos[0]=='%') {
	    inPct = true;
	    widthSet = false;
	    width = 0;
	} else if (!inPct) {   // Normal text
	    // Fast-forward to next escape and add to output
	    const char *ep = pos;
	    while (ep[0] && ep[0]!='%') ep++;
	    if (ep != pos) {
		output += string(pos, ep-pos);
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
	    case '%':
		output += '%';
		break;
	    case 'S': { // "C" string
		const char* cstrp = va_arg(ap, const char*);
		output += cstrp;
		break;
	    }
	    default: {
		// Deal with all read-and-print somethings
		const int lbits = va_arg(ap, int);
		QData ld = 0;
		WDataInP lwp;
		if (lbits <= VL_QUADSIZE) {
		    WData qlwp[2];
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
		    int digits=sprintf(tmp,"%lld",(vlsint64_t)(VL_EXTENDS_QQ(lbits,lbits,ld)));
		    int needmore = width-digits;
		    if (needmore>0) output.append(needmore,' '); // Pre-pad spaces
		    output += tmp;
		    break;
		}
		case 'u': { // Unsigned decimal
		    int digits=sprintf(tmp,"%llu",ld);
		    int needmore = width-digits;
		    if (needmore>0) output.append(needmore,' '); // Pre-pad spaces
		    output += tmp;
		    break;
		}
		case 't': { // Time
		    int digits;
		    if (VL_TIME_MULTIPLIER==1) {
			digits=sprintf(tmp,"%llu",ld);
		    } else if (VL_TIME_MULTIPLIER==1000) {
			digits=sprintf(tmp,"%llu.%03llu",
				       (QData)(ld/VL_TIME_MULTIPLIER),
				       (QData)(ld%VL_TIME_MULTIPLIER));
		    } else {
			vl_fatal(__FILE__,__LINE__,"","%%Error: Unsupported VL_TIME_MULTIPLIER");
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
		    string msg = string("%%Error: Unknown _vl_vsformat code: ")+pos[0]+"\n";
		    vl_fatal(__FILE__,__LINE__,"",msg.c_str());
		    break;
		} // switch
	    }
	    } // switch
	}
    }
}

static inline bool _vl_vsss_eof(FILE* fp, int& floc) {
    return fp ? feof(fp) : (floc<0);
}
static inline void _vl_vsss_advance(FILE* fp, int& floc) {
    if (fp) fgetc(fp);
    else floc -= 8;
}
static inline int  _vl_vsss_peek(FILE* fp, int& floc, WDataInP fromp) {
    // Get a character without advancing
    if (fp) {
	int data = fgetc(fp);
	if (data == EOF) return EOF;
	ungetc(data,fp);
	return data;
    } else {
	if (floc < 0) return EOF;
	floc = floc & ~7;	// Align to closest character
	int data = (fromp[VL_BITWORD_I(floc)] >> VL_BITBIT_I(floc)) & 0xff;
	return data;
    }
}
static inline void _vl_vsss_skipspace(FILE* fp, int& floc, WDataInP fromp) {
    while (1) {
	int c = _vl_vsss_peek(fp, floc, fromp);
	if (c==EOF || !isspace(c)) return;
	_vl_vsss_advance(fp, floc);
    }
}
static inline void _vl_vsss_read(FILE* fp, int& floc, WDataInP fromp,
				 char* tmpp, const char* acceptp) {
    // Read into tmp, consisting of characters from acceptp list
    char* cp = tmpp;
    while (1) {
	int c = _vl_vsss_peek(fp, floc, fromp);
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

IData _vl_vsscanf(FILE* fp,  // If a fscanf
		  int fbits, WDataInP fromp,  // Else if a sscanf
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
	//VL_PRINTF("_vlscan fmt='%c' floc=%d file='%c'\n", pos[0], floc, _vl_vsss_peek(fp,floc,fromp));
	if (!inPct && pos[0]=='%') {
	    inPct = true;
	} else if (!inPct && isspace(pos[0])) {   // Format spaces
	    while (isspace(pos[1])) pos++;
	    _vl_vsss_skipspace(fp,floc,fromp);
	} else if (!inPct) {   // Expected Format
	    _vl_vsss_skipspace(fp,floc,fromp);
	    int c = _vl_vsss_peek(fp,floc,fromp);
	    if (c != pos[0]) goto done;
	    else _vl_vsss_advance(fp,floc);
	} else { // Format character
	    // Skip loading spaces
	    inPct = false;
	    char fmt = pos[0];
	    switch (fmt) {
	    case '%': {
		int c = _vl_vsss_peek(fp,floc,fromp);
		if (c != '%') goto done;
		else _vl_vsss_advance(fp,floc);
		break;
	    }
	    default: {
		// Deal with all read-and-scan somethings
		// Note LSBs are preserved if there's an overflow
		const int obits = va_arg(ap, int);
		int lsb = 0;
		WData qowp[2];
		WDataOutP owp = qowp;
		if (obits > VL_QUADSIZE) {
		    owp = va_arg(ap,WDataOutP);
		}
		for (int i=0; i<VL_WORDS_I(obits); i++) owp[i] = 0;
		switch (fmt) {
		case 'c': {
		    int c = _vl_vsss_peek(fp,floc,fromp);
		    if (c==EOF) goto done;
		    else _vl_vsss_advance(fp,floc);
		    owp[0] = c;
		    break;
		}
		case 's': {
		    _vl_vsss_skipspace(fp,floc,fromp);
		    _vl_vsss_read(fp,floc,fromp, tmp, NULL);
		    if (!tmp[0]) goto done;
		    int pos = strlen(tmp)-1;
		    for (int i=0; i<obits && pos>=0; pos--) {
			_vl_vsss_setbit(owp,obits,lsb, 8, tmp[pos]); lsb+=8;
		    }
		    break;
		}
		case 'd': { // Signed decimal
		    _vl_vsss_skipspace(fp,floc,fromp);
		    _vl_vsss_read(fp,floc,fromp, tmp, "0123456789+-xz?_");
		    if (!tmp[0]) goto done;
		    vlsint64_t ld;
		    sscanf(tmp,"%lld",&ld);
		    VL_SET_WQ(owp,ld);
		    break;
		}
		case 't': // FALLTHRU  // Time
		case 'u': { // Unsigned decimal
		    _vl_vsss_skipspace(fp,floc,fromp);
		    _vl_vsss_read(fp,floc,fromp, tmp, "0123456789+-xz?_");
		    if (!tmp[0]) goto done;
		    QData ld;
		    sscanf(tmp,"%llu",&ld);
		    VL_SET_WQ(owp,ld);
		    break;
		}
		case 'b': {
		    _vl_vsss_skipspace(fp,floc,fromp);
		    _vl_vsss_read(fp,floc,fromp, tmp, "01xz?_");
		    if (!tmp[0]) goto done;
		    int pos = strlen(tmp)-1;
		    for (int i=0; i<obits && pos>=0; pos--) {
			switch(tmp[pos]) {
			case 'x': case 'z': case '?': //FALLTHRU
			case '0': lsb++; break;
			case '1': _vl_vsss_setbit(owp,obits,lsb, 1, 1); lsb++; break;
			case '_': break;
			}
		    }
		    break;
		}
		case 'o': {
		    _vl_vsss_skipspace(fp,floc,fromp);
		    _vl_vsss_read(fp,floc,fromp, tmp, "01234567xz?_");
		    if (!tmp[0]) goto done;
		    int pos = strlen(tmp)-1;
		    for (int i=0; i<obits && pos>=0; pos--) {
			switch(tmp[pos]) {
			case 'x': case 'z': case '?': //FALLTHRU
			case '0': lsb+=3; break;
			case '1': _vl_vsss_setbit(owp,obits,lsb, 3, 1); lsb+=3; break;
			case '2': _vl_vsss_setbit(owp,obits,lsb, 3, 2); lsb+=3; break;
			case '3': _vl_vsss_setbit(owp,obits,lsb, 3, 3); lsb+=3; break;
			case '4': _vl_vsss_setbit(owp,obits,lsb, 3, 4); lsb+=3; break;
			case '5': _vl_vsss_setbit(owp,obits,lsb, 3, 5); lsb+=3; break;
			case '6': _vl_vsss_setbit(owp,obits,lsb, 3, 6); lsb+=3; break;
			case '7': _vl_vsss_setbit(owp,obits,lsb, 3, 7); lsb+=3; break;
			case '_': break;
			}
		    }
		    break;
		}
		case 'x': {
		    _vl_vsss_skipspace(fp,floc,fromp);
		    _vl_vsss_read(fp,floc,fromp, tmp, "0123456789abcdefxz?_");
		    if (!tmp[0]) goto done;
		    int pos = strlen(tmp)-1;
		    for (int i=0; i<obits && pos>=0; pos--) {
			switch(tmp[pos]) {
			case 'x': case 'z': case '?': //FALLTHRU
			case '0': lsb+=4; break;
			case '1': _vl_vsss_setbit(owp,obits,lsb, 4,  1); lsb+=4; break;
			case '2': _vl_vsss_setbit(owp,obits,lsb, 4,  2); lsb+=4; break;
			case '3': _vl_vsss_setbit(owp,obits,lsb, 4,  3); lsb+=4; break;
			case '4': _vl_vsss_setbit(owp,obits,lsb, 4,  4); lsb+=4; break;
			case '5': _vl_vsss_setbit(owp,obits,lsb, 4,  5); lsb+=4; break;
			case '6': _vl_vsss_setbit(owp,obits,lsb, 4,  6); lsb+=4; break;
			case '7': _vl_vsss_setbit(owp,obits,lsb, 4,  7); lsb+=4; break;
			case '8': _vl_vsss_setbit(owp,obits,lsb, 4,  8); lsb+=4; break;
			case '9': _vl_vsss_setbit(owp,obits,lsb, 4,  9); lsb+=4; break;
			case 'a': _vl_vsss_setbit(owp,obits,lsb, 4, 10); lsb+=4; break;
			case 'b': _vl_vsss_setbit(owp,obits,lsb, 4, 11); lsb+=4; break;
			case 'c': _vl_vsss_setbit(owp,obits,lsb, 4, 12); lsb+=4; break;
			case 'd': _vl_vsss_setbit(owp,obits,lsb, 4, 13); lsb+=4; break;
			case 'e': _vl_vsss_setbit(owp,obits,lsb, 4, 14); lsb+=4; break;
			case 'f': _vl_vsss_setbit(owp,obits,lsb, 4, 15); lsb+=4; break;
			case '_': break;
			}
		    }
		    break;
		}
		default:
		    string msg = string("%%Error: Unknown _vl_vsscanf code: ")+pos[0]+"\n";
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

void _VL_VINT_TO_STRING(int obits, char* destoutp, WDataInP sourcep) {
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
    *destp++ = '\0'; // Terminate
    while (isspace(*(destp-1)) && destp>destoutp) *--destp = '\0';  // Drop trailing spaces
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

IData VL_FGETS_IXQ(int obits, void* destp, QData fpq) {
    FILE* fp = VL_CVT_Q_FP(fpq);
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

QData VL_FOPEN_QI(QData filename, IData mode) {
    IData fnw[2];  VL_SET_WQ(fnw, filename);
    return VL_FOPEN_WI(2, fnw, mode);
}
QData VL_FOPEN_WI(int fnwords, WDataInP filenamep, IData mode) {
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(fnwords*VL_WORDSIZE, filenamez, filenamep);
    char modez[5];
    _VL_VINT_TO_STRING(VL_WORDSIZE, modez, &mode);
    return VL_CVT_FP_Q(fopen(filenamez,modez));
}

void VL_WRITEF(const char* formatp, ...) {
    va_list ap;
    va_start(ap,formatp);
    string output;
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    // Users can redefine VL_PRINTF if they wish.
    VL_PRINTF("%s", output.c_str());
}

void VL_FWRITEF(QData fpq, const char* formatp, ...) {
    FILE* fp = VL_CVT_Q_FP(fpq);
    if (VL_UNLIKELY(!fp)) return;

    va_list ap;
    va_start(ap,formatp);
    string output;
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    fputs(output.c_str(), fp);
}

IData VL_FSCANF_IX(QData fpq, const char* formatp, ...) {
    FILE* fp = VL_CVT_Q_FP(fpq);
    if (VL_UNLIKELY(!fp)) return 0;

    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(fp, 0, NULL, formatp, ap);
    va_end(ap);
    return got;
}

IData VL_SSCANF_IIX(int lbits, IData ld, const char* formatp, ...) {
    IData fnw[2];  VL_SET_WI(fnw, ld);

    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, lbits, fnw, formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IQX(int lbits, QData ld, const char* formatp, ...) {
    IData fnw[2];  VL_SET_WQ(fnw, ld);

    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, lbits, fnw, formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IWX(int lbits, WDataInP lwp, const char* formatp, ...) {
    va_list ap;
    va_start(ap,formatp);
    IData got = _vl_vsscanf(NULL, lbits, lwp, formatp, ap);
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
    if (!fp) {
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
	if (c==EOF) break;
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
		    if (addr >= (IData)(depth+array_lsb) || addr < (IData)(array_lsb)) {
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
			    _VL_SHIFTL_INPLACE_W(width, datap, shift);
			    datap[0] |= value;
			}
			if (value>=(1<<shift)) {
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
    if (end != (IData)(~ VL_ULL(0))  && addr != (end+1)) {
	vl_fatal (ofilenamez, linenum, "", "$readmem file ended before specified ending-address");
    }
}

//===========================================================================
// Verilated:: Methods

const char* Verilated::catName(const char* n1, const char* n2) {
    // Returns new'ed data
    // Used by symbol table creation to make module names
    static char* strp = NULL;
    static int   len  = -1;
    int newlen = strlen(n1)+strlen(n2)+2;
    if (newlen > len) {
	if (strp) delete [] strp;
	strp = new char[newlen];
	len = newlen;
    }
    strcpy(strp,n1);
    strcat(strp,n2);
    return strp;
}

//===========================================================================
// VerilatedModule:: Methods

VerilatedModule::VerilatedModule(const char* namep)
    : m_namep(strdup(namep)) {
}

VerilatedModule::~VerilatedModule() {
    if (m_namep) free((void*)m_namep); m_namep=NULL;
}

//===========================================================================
