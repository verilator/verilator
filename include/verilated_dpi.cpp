// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2017 by Wilson Snyder. This program is free software; you can
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
/// \brief Verilator: DPI implementation code
///
///     This file must be compiled and linked against all objects
///     created from Verilator or called by Verilator that use the DPI.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#define _VERILATED_DPI_CPP_
#include "verilatedos.h"
#include "verilated_dpi.h"
#include "verilated_imp.h"

// On MSVC++ we need svdpi.h to declare exports, not imports
#define DPI_PROTOTYPES
#undef XXTERN
#define XXTERN DPI_EXTERN DPI_DLLESPEC
#undef EETERN
#define EETERN DPI_EXTERN DPI_DLLESPEC

#include "vltstd/svdpi.h"

//======================================================================
// Internal macros

// Not supported yet
#define _VL_SVDPI_UNIMP() \
    VL_FATAL_MT(__FILE__,__LINE__,"",(std::string("%%Error: Unsupported DPI function: ")+VL_FUNC).c_str())

// Function requires a "context" in the import declaration
#define _VL_SVDPI_CONTEXT_WARN() \
    VL_PRINTF_MT("%%Warning: DPI C Function called by Verilog DPI import with missing 'context' keyword.\n");

//======================================================================
//======================================================================
//======================================================================
// DPI ROUTINES

const char* svDpiVersion() {
    return "1800-2005";
}

//======================================================================
// Bit-select utility functions.

svBit svGetBitselBit(const svBitVecVal* sp, int bit) {
    return VL_BITRSHIFT_W(sp,bit) & 1;
}
svLogic svGetBitselLogic(const svLogicVecVal* sp, int bit) {
    // Not VL_BITRSHIFT_W as sp is a different structure type
    // Verilator doesn't support X/Z so only aval
    return (sp[VL_BITWORD_I(bit)].aval >> VL_BITBIT_I(bit)) & 1;
}

void svPutBitselBit(svBitVecVal* dp, int bit, svBit s) {
    VL_ASSIGNBIT_WI(32, bit, dp, s);
}
void svPutBitselLogic(svLogicVecVal* dp, int bit, svLogic s) {
    // Verilator doesn't support X/Z so only aval
    dp[VL_BITWORD_I(bit)].aval
        = ((dp[VL_BITWORD_I(bit)].aval & ~(VL_UL(1)<<VL_BITBIT_I(bit)))
           | ((s&1)<<VL_BITBIT_I(bit)));
}

void svGetPartselBit(svBitVecVal* dp, const svBitVecVal* sp, int lsb, int width) {
    // See also VL_SEL_WWI
    int msb = lsb+width-1;
    int word_shift = VL_BITWORD_I(lsb);
    if (VL_BITBIT_I(lsb)==0) {
        // Just a word extract
        for (int i=0; i<VL_WORDS_I(width); ++i) dp[i] = sp[i+word_shift];
    } else {
        int loffset = lsb & VL_SIZEBITS_I;
        int nbitsfromlow = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int words = VL_WORDS_I(msb-lsb+1);
        for (int i=0; i<words; ++i) {
            dp[i] = sp[i+word_shift]>>loffset;
            int upperword = i+word_shift+1;
            if (upperword <= static_cast<int>(VL_BITWORD_I(msb))) {
                dp[i] |= sp[upperword] << nbitsfromlow;
            }
        }
    }
    // Clean result
    dp[VL_WORDS_I(width)-1] &= VL_MASK_I(width);
}
void svGetPartselLogic(svLogicVecVal* dp, const svLogicVecVal* sp, int lsb, int width) {
    int msb = lsb+width-1;
    int word_shift = VL_BITWORD_I(lsb);
    if (VL_BITBIT_I(lsb)==0) {
        // Just a word extract
        for (int i=0; i<VL_WORDS_I(width); ++i) dp[i] = sp[i+word_shift];
    } else {
        int loffset = lsb & VL_SIZEBITS_I;
        int nbitsfromlow = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int words = VL_WORDS_I(msb-lsb+1);
        for (int i=0; i<words; ++i) {
            dp[i].aval = sp[i+word_shift].aval >> loffset;
            dp[i].bval = sp[i+word_shift].bval >> loffset;
            int upperword = i+word_shift+1;
            if (upperword <= static_cast<int>(VL_BITWORD_I(msb))) {
                dp[i].aval |= sp[upperword].aval << nbitsfromlow;
                dp[i].bval |= sp[upperword].bval << nbitsfromlow;
            }
        }
    }
    // Clean result
    dp[VL_WORDS_I(width)-1].aval &= VL_MASK_I(width);
    dp[VL_WORDS_I(width)-1].bval &= VL_MASK_I(width);
}
void svPutPartselBit(svBitVecVal* dp, const svBitVecVal* sp, int lbit, int width) {
    // See also _VL_INSERT_WW
    int hbit = lbit+width-1;
    int hoffset = hbit & VL_SIZEBITS_I;
    int loffset = lbit & VL_SIZEBITS_I;
    int lword = VL_BITWORD_I(lbit);
    int words = VL_WORDS_I(hbit-lbit+1);
    if (hoffset==VL_SIZEBITS_I && loffset==0) {
        // Fast and common case, word based insertion
        for (int i=0; i<words; ++i) {
            dp[lword+i] = sp[i];
        }
    }
    else if (loffset==0) {
        // Non-32bit, but nicely aligned, so stuff all but the last word
        for (int i=0; i<(words-1); ++i) {
            dp[lword+i] = sp[i];
        }
        IData hinsmask = (VL_MASK_I(hoffset-0+1)); // Know it's not a full word as above fast case handled it
        dp[lword+words-1] = (dp[words+lword-1] & ~hinsmask) | (sp[words-1] & hinsmask);
    }
    else {
        IData hinsmask = (VL_MASK_I(hoffset-0+1))<<0;
        IData linsmask = (VL_MASK_I(31-loffset+1))<<loffset;
        int nbitsonright = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int hword = VL_BITWORD_I(hbit);
        for (int i=0; i<words; ++i) {
            {   // Lower word
                int oword = lword+i;
                IData d = sp[i]<<loffset;
                IData od = (dp[oword] & ~linsmask) | (d & linsmask);
                if (oword==hword) dp[oword] = (dp[oword] & ~hinsmask) | (od & hinsmask);
                else dp[oword] = od;
            }
            {   // Upper word
                int oword = lword+i+1;
                if (oword <= hword) {
                    IData d = sp[i]>>nbitsonright;
                    IData od = (d & ~linsmask) | (dp[oword] & linsmask);
                    if (oword==hword) dp[oword] = (dp[oword] & ~hinsmask) | (od & hinsmask);
                    else dp[oword] = od;
                }
            }
        }
    }
}
void svPutPartselLogic(svLogicVecVal* dp, const svLogicVecVal* sp, int lbit, int width) {
    int hbit = lbit+width-1;
    int hoffset = hbit & VL_SIZEBITS_I;
    int loffset = lbit & VL_SIZEBITS_I;
    int lword = VL_BITWORD_I(lbit);
    int words = VL_WORDS_I(hbit-lbit+1);
    if (hoffset==VL_SIZEBITS_I && loffset==0) {
        // Fast and common case, word based insertion
        for (int i=0; i<words; ++i) {
            dp[lword+i].aval = sp[i].aval;
            dp[lword+i].bval = sp[i].bval;
        }
    }
    else if (loffset==0) {
        // Non-32bit, but nicely aligned, so stuff all but the last word
        for (int i=0; i<(words-1); ++i) {
            dp[lword+i].aval = sp[i].aval;
            dp[lword+i].bval = sp[i].bval;
        }
        IData hinsmask = (VL_MASK_I(hoffset-0+1)); // Know it's not a full word as above fast case handled it
        dp[lword+words-1].aval = (dp[words+lword-1].aval & ~hinsmask) | (sp[words-1].aval & hinsmask);
        dp[lword+words-1].bval = (dp[words+lword-1].bval & ~hinsmask) | (sp[words-1].bval & hinsmask);
    }
    else {
        IData hinsmask = (VL_MASK_I(hoffset-0+1))<<0;
        IData linsmask = (VL_MASK_I(31-loffset+1))<<loffset;
        int nbitsonright = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int hword = VL_BITWORD_I(hbit);
        for (int i=0; i<words; ++i) {
            {   // Lower word
                int oword = lword+i;
                IData d_a = sp[i].aval << loffset;
                IData d_b = sp[i].bval << loffset;
                IData od_a = (dp[oword].aval & ~linsmask) | (d_a & linsmask);
                IData od_b = (dp[oword].bval & ~linsmask) | (d_b & linsmask);
                if (oword==hword) {
                    dp[oword].aval = (dp[oword].aval & ~hinsmask) | (od_a & hinsmask);
                    dp[oword].bval = (dp[oword].bval & ~hinsmask) | (od_b & hinsmask);
                } else {
                    dp[oword].aval = od_a;
                    dp[oword].bval = od_b;
                }
            }
            {   // Upper word
                int oword = lword+i+1;
                if (oword <= hword) {
                    IData d_a = sp[i].aval >> nbitsonright;
                    IData d_b = sp[i].bval >> nbitsonright;
                    IData od_a = (d_a & ~linsmask) | (dp[oword].aval & linsmask);
                    IData od_b = (d_b & ~linsmask) | (dp[oword].bval & linsmask);
                    if (oword==hword) {
                        dp[oword].aval = (dp[oword].aval & ~hinsmask) | (od_a & hinsmask);
                        dp[oword].bval = (dp[oword].bval & ~hinsmask) | (od_b & hinsmask);
                    } else {
                        dp[oword].aval = od_a;
                        dp[oword].bval = od_b;
                    }
                }
            }
        }
    }
}

//======================================================================
// Open array querying functions

int svLeft(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svRight(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svLow(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svHigh(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svIncrement(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svSize(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svDimensions(const svOpenArrayHandle h) {
    _VL_SVDPI_UNIMP(); return 0;
}
void* svGetArrayPtr(const svOpenArrayHandle h) {
    _VL_SVDPI_UNIMP(); return NULL;
}
int svSizeOfArray(const svOpenArrayHandle h) {
    _VL_SVDPI_UNIMP(); return 0;
}

void* svGetArrElemPtr(const svOpenArrayHandle h, int indx1, ...) {
    _VL_SVDPI_UNIMP(); return NULL;
}
void* svGetArrElemPtr1(const svOpenArrayHandle h, int indx1) {
    _VL_SVDPI_UNIMP(); return NULL;
}
void* svGetArrElemPtr2(const svOpenArrayHandle h, int indx1, int indx2) {
    _VL_SVDPI_UNIMP(); return NULL;
}
void* svGetArrElemPtr3(const svOpenArrayHandle h, int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP(); return NULL;
}

//======================================================================
// s=source, d=destination
// From user space into simulator storage

void svPutBitArrElemVecVal(const svOpenArrayHandle d, const svBitVecVal* s,
                           int indx1, ...) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem1VecVal(const svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem2VecVal(const svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem3VecVal(const svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElemVecVal(const svOpenArrayHandle d, const svLogicVecVal* s,
                             int indx1, ...) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElem1VecVal(const svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElem2VecVal(const svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElem3VecVal(const svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP();
}

//======================================================================
// From simulator storage into user space

void svGetBitArrElemVecVal(svBitVecVal* d, const svOpenArrayHandle s,
                           int indx1, ...) {
    _VL_SVDPI_UNIMP();
}
void svGetBitArrElem1VecVal(svBitVecVal* d, const svOpenArrayHandle s,
                            int indx1) {
    _VL_SVDPI_UNIMP();
}
void svGetBitArrElem2VecVal(svBitVecVal* d, const svOpenArrayHandle s,
                            int indx1, int indx2) {
    _VL_SVDPI_UNIMP();
}
void svGetBitArrElem3VecVal(svBitVecVal* d, const svOpenArrayHandle s,
                            int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP();
}
void svGetLogicArrElemVecVal(svLogicVecVal* d, const svOpenArrayHandle s,
                             int indx1, ...) {
    _VL_SVDPI_UNIMP();
}
void svGetLogicArrElem1VecVal(svLogicVecVal* d, const svOpenArrayHandle s,
                              int indx1) {
    _VL_SVDPI_UNIMP();
}
void svGetLogicArrElem2VecVal(svLogicVecVal* d, const svOpenArrayHandle s,
                              int indx1, int indx2) {
    _VL_SVDPI_UNIMP();
}
void svGetLogicArrElem3VecVal(svLogicVecVal* d, const svOpenArrayHandle s,
                              int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP();
}

svBit svGetBitArrElem(const svOpenArrayHandle s, int indx1, ...) {
    _VL_SVDPI_UNIMP(); return 0;
}
svBit svGetBitArrElem1(const svOpenArrayHandle s, int indx1) {
    _VL_SVDPI_UNIMP(); return 0;
}
svBit svGetBitArrElem2(const svOpenArrayHandle s, int indx1, int indx2) {
    _VL_SVDPI_UNIMP(); return 0;
}
svBit svGetBitArrElem3(const svOpenArrayHandle s, int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP(); return 0;
}
svLogic svGetLogicArrElem(const svOpenArrayHandle s, int indx1, ...) {
    _VL_SVDPI_UNIMP(); return sv_x;
}
svLogic svGetLogicArrElem1(const svOpenArrayHandle s, int indx1) {
    _VL_SVDPI_UNIMP(); return sv_x;
}
svLogic svGetLogicArrElem2(const svOpenArrayHandle s, int indx1, int indx2) {
    _VL_SVDPI_UNIMP(); return sv_x;
}
svLogic svGetLogicArrElem3(const svOpenArrayHandle s, int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP(); return sv_x;
}
void svPutLogicArrElem(const svOpenArrayHandle d, svLogic value, int indx1, ...) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElem1(const svOpenArrayHandle d, svLogic value, int indx1) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElem2(const svOpenArrayHandle d, svLogic value, int indx1, int indx2) {
    _VL_SVDPI_UNIMP();
}
void svPutLogicArrElem3(const svOpenArrayHandle d, svLogic value, int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem(const svOpenArrayHandle d, svBit value, int indx1, ...) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem1(const svOpenArrayHandle d, svBit value, int indx1) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem2(const svOpenArrayHandle d, svBit value, int indx1, int indx2) {
    _VL_SVDPI_UNIMP();
}
void svPutBitArrElem3(const svOpenArrayHandle d, svBit value, int indx1, int indx2, int indx3) {
    _VL_SVDPI_UNIMP();
}

//======================================================================
// Functions for working with DPI context

svScope svGetScope() {
    if (VL_UNLIKELY(!Verilated::dpiInContext())) { _VL_SVDPI_CONTEXT_WARN(); return NULL; }
    return (svScope)Verilated::dpiScope();
}

svScope svSetScope(const svScope scope) {
    const VerilatedScope* prevScopep = Verilated::dpiScope();
    const VerilatedScope* vscopep = reinterpret_cast<const VerilatedScope*>(scope);
    Verilated::dpiScope(vscopep);
    return (svScope)prevScopep;
}

const char* svGetNameFromScope(const svScope scope) {
    const VerilatedScope* vscopep = reinterpret_cast<const VerilatedScope*>(scope);
    return vscopep->name();
}

svScope svGetScopeFromName(const char* scopeName) {
    return (svScope)VerilatedImp::scopeFind(scopeName);
}

int svPutUserData(const svScope scope, void* userKey, void* userData) {
    VerilatedImp::userInsert(scope,userKey,userData);
    return 0;
}

void* svGetUserData(const svScope scope, void* userKey) {
    return VerilatedImp::userFind(scope,userKey);
}

int svGetCallerInfo(const char** fileNamepp, int *lineNumberp) {
    if (VL_UNLIKELY(!Verilated::dpiInContext())) { _VL_SVDPI_CONTEXT_WARN(); return false; }
    if (VL_LIKELY(fileNamepp)) *fileNamepp = Verilated::dpiFilenamep();  // thread local
    if (VL_LIKELY(lineNumberp)) *lineNumberp = Verilated::dpiLineno();  // thread local
    return true;
}

//======================================================================
// Disables

int svIsDisabledState() {
    return 0; // Disables not implemented
}

void svAckDisabledState() {
    // Disables not implemented
}
