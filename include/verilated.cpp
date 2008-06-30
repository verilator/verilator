// -*- C++ -*-
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
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
    return (rand()<<16) | rand();
#else
    return (lrand48()<<16) | lrand48();
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
    // Note uses a single buffer internally; presumes only one usage per printf
    static VL_THREAD char str[VL_VALUE_STRING_MAX_WIDTH];
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
		int bits = va_arg(ap, int);
		QData ld = 0;
		WDataInP lwp;
		if (bits <= VL_QUADSIZE) {
		    WData qlwp[2];
		    ld = _VL_VA_ARG_Q(ap, bits);
		    VL_SET_WQ(qlwp,ld);
		    lwp = qlwp;
		} else {
		    lwp = va_arg(ap,WDataInP);
		    ld = lwp[0];
		    if (fmt == 'u' || fmt == 'd') fmt = 'x';  // Not supported, but show something
		}
		int lsb=bits-1;
		if (widthSet && width==0) while (lsb && !VL_BITISSET_W(lwp,lsb)) lsb--;
		switch (fmt) {
		case 'b':
		    for (; lsb>=0; lsb--) {
			output += ((lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 1) + '0';
		    }
		    break;
		case 'c': {
		    IData charval = ld & 0xff;
		    output += charval;
		    break;
		}
		case 'd': { // Signed decimal
		    int digits=sprintf(str,"%lld",(vlsint64_t)(VL_EXTENDS_QQ(bits,bits,ld)));
		    int needmore = width-digits;
		    if (needmore>0) output.append(needmore,' '); // Pre-pad spaces
		    output += str;
		    break;
		}
		case 'o':
		    for (; lsb>=0; lsb--) {
			lsb = (lsb / 3) * 3; // Next digit
			// Octal numbers may span more than one wide word,
			// so we need to grab each bit separately and check for overrun
			// Octal is rare, so we'll do it a slow simple way
			output += ('0'
				   + ((VL_BITISSETLIMIT_W(lwp, bits, lsb+0)) ? 1 : 0)
				   + ((VL_BITISSETLIMIT_W(lwp, bits, lsb+1)) ? 2 : 0)
				   + ((VL_BITISSETLIMIT_W(lwp, bits, lsb+2)) ? 4 : 0));
		    }
		    break;
		case 's':
		    for (; lsb>=0; lsb--) {
			lsb = (lsb / 8) * 8; // Next digit
			IData charval = (lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xff;
			output += (charval==0)?' ':charval;
		    }
		    break;
		case 'u': { // Unsigned decimal
		    int digits=sprintf(str,"%llu",ld);
		    int needmore = width-digits;
		    if (needmore>0) output.append(needmore,' '); // Pre-pad spaces
		    output += str;
		    break;
		}
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
    char buffer[bytes];

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
