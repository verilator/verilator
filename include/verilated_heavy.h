// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2017 by Wilson Snyder. This program is free software; you can
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
///
/// \file
/// \brief Verilator: String include for all Verilated C files
///
///	This file is included automatically by Verilator at the top of
///	all C++ files it generates.  It is used when strings or other
///	heavyweight types are required; these contents are not part of
///	verilated.h to save compile time when such types aren't used.
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_HEAVY_H_
#define _VERILATED_HEAVY_H_ 1 ///< Header Guard

#include "verilated.h"

#include <string>

//======================================================================
// Conversion functions

extern std::string VL_CVT_PACK_STR_NW(int lwords, WDataInP lwp);
inline std::string VL_CVT_PACK_STR_NQ(QData lhs) {
    WData lw[2];  VL_SET_WQ(lw, lhs);
    return VL_CVT_PACK_STR_NW(2, lw);
}
inline std::string VL_CVT_PACK_STR_NN(const std::string& lhs) {
    return lhs;
}
inline std::string VL_CVT_PACK_STR_NI(IData lhs) {
    WData lw[1];  lw[0] = lhs;
    return VL_CVT_PACK_STR_NW(1, lw);
}
inline std::string VL_CONCATN_NNN(const std::string& lhs, const std::string& rhs) {
    return lhs+rhs;
}
inline std::string VL_REPLICATEN_NNQ(int,int,int, const std::string& lhs, IData rep) {
    std::string out; out.reserve(lhs.length() * rep);
    for (unsigned times=0; times<rep; ++times) out += lhs;
    return out;
}
inline std::string VL_REPLICATEN_NNI(int obits,int lbits,int rbits, const std::string& lhs, IData rep) {
    return VL_REPLICATEN_NNQ(obits,lbits,rbits,lhs,rep);
}

extern IData VL_FOPEN_NI(const std::string& filename, IData mode);
extern void VL_READMEM_N(bool hex, int width, int depth, int array_lsb, int fnwords,
                         const std::string& ofilename, void* memp, IData start, IData end);
extern IData VL_SSCANF_INX(int lbits, const std::string& ld, const char* formatp, ...);
extern void VL_SFORMAT_X(int obits_ignored, std::string &output, const char* formatp, ...);
extern std::string VL_SFORMATF_NX(const char* formatp, ...);
extern IData VL_VALUEPLUSARGS_INW(int rbits, const std::string& ld, WDataOutP rdp);
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, IData& rdr) {
    WData rwp[2];  // WData must always be at least 2
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INQ(int rbits, const std::string& ld, QData& rdr) {
    WData rwp[2];
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = VL_SET_QW(rwp);
    return got;
}
extern IData VL_VALUEPLUSARGS_INN(int, const std::string& ld, std::string& rdr);

#endif // Guard
