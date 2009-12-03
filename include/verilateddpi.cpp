// -*- C++ -*-
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
//=========================================================================
///
/// \file
/// \brief Verilator: DPI implementation code
///
///	This file must be compiled and linked against all objects
///	created from Verilator or called by Verilator that use the DPI.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#include "verilatedos.h"
#include "verilated.h"
#include "svdpi.h"

//======================================================================
// Internal macros

#define _VL_SVDPI_UNIMP()

// Function requires a "context" in the import declaration
#define _VL_SVDPI_CONTEXT_WARN()

//======================================================================
// Version

const char* svDpiVersion() {
    return "P1800-2005";
}

//======================================================================
// Bit-select utility functions.

svBit svGetBitselBit(const svBitVecVal* s, int i) {
    _VL_SVDPI_UNIMP(); return 0;
}
svLogic svGetBitselLogic(const svLogicVecVal* s, int i) {
    _VL_SVDPI_UNIMP(); return 0;
}

void svPutBitselBit(svBitVecVal* d, int i, svBit s) {
    _VL_SVDPI_UNIMP();
}
void svPutBitselLogic(svLogicVecVal* d, int i, svLogic s) {
    _VL_SVDPI_UNIMP();
}

void svGetPartselBit(svBitVecVal* d, const svBitVecVal* s, int i, int w) {
    _VL_SVDPI_UNIMP();
}
void svGetPartselLogic(svLogicVecVal* d, const svLogicVecVal* s, int i, int w) {
    _VL_SVDPI_UNIMP();
}

void svPutPartselBit(svBitVecVal* d, const svBitVecVal s, int i, int w) {
    _VL_SVDPI_UNIMP();
}
void svPutPartselLogic(svLogicVecVal* d, const svLogicVecVal s, int i, int w) {
    _VL_SVDPI_UNIMP();
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
int svLength(const svOpenArrayHandle h, int d) {
    _VL_SVDPI_UNIMP(); return 0;
}
int svDimensions(const svOpenArrayHandle h) {
    _VL_SVDPI_UNIMP(); return 0;
}

void *svGetArrayPtr(const svOpenArrayHandle) {
    _VL_SVDPI_UNIMP(); return NULL;
}

int svSizeOfArray(const svOpenArrayHandle) {
    _VL_SVDPI_UNIMP(); return 0;
}

void *svGetArrElemPtr(const svOpenArrayHandle, int indx1, ...) {
    _VL_SVDPI_UNIMP(); return NULL;
}
void *svGetArrElemPtr1(const svOpenArrayHandle, int indx1) {
    _VL_SVDPI_UNIMP(); return NULL;
}
void *svGetArrElemPtr2(const svOpenArrayHandle, int indx1, int indx2) {
    _VL_SVDPI_UNIMP(); return NULL;
}
void *svGetArrElemPtr3(const svOpenArrayHandle, int indx1, int indx2, int indx3) {
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
    _VL_SVDPI_UNIMP(); return NULL;
}

svScope svSetScope(const svScope scope) {
    _VL_SVDPI_UNIMP(); return NULL;
}

const char* svGetNameFromScope(const svScope) {
    _VL_SVDPI_UNIMP(); return "";
}

svScope svGetScopeFromName(const char* scopeName) {
    _VL_SVDPI_UNIMP(); return NULL;
}

int svPutUserData(const svScope scope, void *userKey, void* userData) {
    _VL_SVDPI_UNIMP();
    return -1;  // -1 == error
}

void* svGetUserData(const svScope scope, void* userKey) {
    return NULL;  // NULL == error
}

int svGetCallerInfo(const char** fileNamepp, int *lineNumberp) {
    _VL_SVDPI_UNIMP(); return false;
    //UNSUP if (!Verilated::dpiInContext) { _VL_SVDPI_CONTEXT_WARN(); return false; }
    //UNSUP if (fileNamep) *fileNamepp = Verilated::dpiFilenamep;  // thread local
    //UNSUP if (lineNumberp) *lineNumberp = Verilated::dpiLineno;  // thread local
    //UNSUP return true;
}

//======================================================================
// Disables

int svIsDisabledState() {
    return 0; // Disables not implemented
}

void svAckDisabledState() {
    // Disables not implemented
}
