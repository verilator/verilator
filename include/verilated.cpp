// $Id$ -*- C++ -*-
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
/// Code available from: http://www.veripool.com/verilator
///
//=========================================================================

#include "verilated.h"
#include <string.h>
#include <ctype.h>

#define VL_VALUE_STRING_MAX_WIDTH 1024	///< Max static char array for VL_VALUE_STRING

//===========================================================================
// Global variables

int  Verilated::s_randReset = false;
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
#ifdef _MSC_VER
    return (rand()<<16) | rand();
#else
    return (lrand48()<<16) | lrand48();
#endif
}

IData VL_RAND_RESET_I(int outBits) {
    if (Verilated::randReset()==0) return 0;
    IData data = ~0;
    if (Verilated::randReset()!=1) {	// if 2, randomize
	data = VL_RAND32();
    }
    if (outBits<32) data &= VL_MASK_I(outBits); 
    return data;
}

QData VL_RAND_RESET_Q(int outBits) {
    if (Verilated::randReset()==0) return 0;
    QData data = VL_ULL(~0);
    if (Verilated::randReset()!=1) {	// if 2, randomize
	data = ((QData)VL_RAND32()<<VL_ULL(32)) | (QData)VL_RAND32();
    }
    if (outBits<64) data &= VL_MASK_Q(outBits); 
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

const char* VL_VALUE_FORMATTED_Q(int obits, char fmt, bool drop0, QData ld) {
    // Convert value into %b/%o/%x/%s/%u/%d formatted string
    // Note uses a single buffer; presumes only one call per printf
    static VL_THREAD char str[VL_VALUE_STRING_MAX_WIDTH];
    char* strp = &str[0];
    int lsb=obits-1;
    if (drop0) while (lsb && !VL_BITISSET_Q(ld,lsb)) lsb--;
    switch (fmt) {
    case 'd':
	sprintf(str,"%lld",(vlsint64_t)(VL_EXTENDS_QQ(obits,obits,ld)));
	return str;
    case 'u':
	sprintf(str,"%llu",ld);
	return str;
    case 's':
	for (; lsb>=0; lsb--) {
	    lsb = (lsb / 8) * 8; // Next digit
	    IData charval = (ld>>VL_BITBIT_Q(lsb)) & 0xff;
	    *strp++ = (charval==0)?' ':charval;
	}
	*strp++ = '\0';
	return str;
    case 'b':
	for (; lsb>=0; lsb--) {
	    *strp++ = ((ld>>VL_BITBIT_Q(lsb)) & 1) + '0';
	}
	*strp++ = '\0';
	return str;
    case 'o':
	for (; lsb>=0; lsb--) {
	    lsb = (lsb / 3) * 3; // Next digit
	    *strp++ = ((ld>>VL_BITBIT_Q(lsb)) & 7) + '0';
	}
	*strp++ = '\0';
	return str;
    default:
	for (; lsb>=0; lsb--) {
	    lsb = (lsb / 4) * 4; // Next digit
	    IData charval = (ld>>VL_BITBIT_Q(lsb)) & 0xf;
	    *strp++ = (charval + ((charval < 10) ? '0':('a'-10)));
	}
	*strp++ = '\0';
	return str;
    }
    *strp++ = '\0';
    return str;
}

const char* VL_VALUE_FORMATTED_W(int obits, char fmt, bool drop0, WDataInP lwp) {
    // Convert value into %b/%o/%x/%s/%u/%d formatted string
    // Note uses a single buffer; presumes only one call per printf
    static VL_THREAD char str[VL_VALUE_STRING_MAX_WIDTH];
    char* strp = &str[0];
    int lsb=obits-1;
    if (drop0) while (lsb && !VL_BITISSET_W(lwp,lsb)) lsb--;
    switch (fmt) {
    case 's':
	for (; lsb>=0; lsb--) {
	    lsb = (lsb / 8) * 8; // Next digit
	    IData charval = (lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xff;
	    *strp++ = (charval==0)?' ':charval;
	}
	*strp++ = '\0';
	return str;
    case 'b':
	for (; lsb>=0; lsb--) {
	    *strp++ = ((lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 1) + '0';
	}
	*strp++ = '\0';
	return str;
    case 'o':
	for (; lsb>=0; lsb--) {
	    lsb = (lsb / 3) * 3; // Next digit
	    *strp++ = ((lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 7) + '0';
	}
	*strp++ = '\0';
	return str;
    default:
	for (; lsb>=0; lsb--) {
	    lsb = (lsb / 4) * 4; // Next digit
	    IData charval = (lwp[VL_BITWORD_I(lsb)]>>VL_BITBIT_I(lsb)) & 0xf;
	    *strp++ = (charval + ((charval < 10) ? '0':('a'-10)));
	}
	*strp++ = '\0';
	return str;
    }
    *strp++ = '\0';
    return str;
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
