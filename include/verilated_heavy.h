// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2019 by Wilson Snyder. This program is free software; you can
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
///     This file is included automatically by Verilator at the top of
///     all C++ files it generates.  It is used when strings or other
///     heavyweight types are required; these contents are not part of
///     verilated.h to save compile time when such types aren't used.
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_HEAVY_H_
#define _VERILATED_HEAVY_H_ 1  ///< Header Guard

#include "verilated.h"

#include <string>

//======================================================================
// Conversion functions

extern std::string VL_CVT_PACK_STR_NW(int lwords, WDataInP lwp) VL_MT_SAFE;
inline std::string VL_CVT_PACK_STR_NQ(QData lhs) VL_PURE {
    WData lw[2];  VL_SET_WQ(lw, lhs);
    return VL_CVT_PACK_STR_NW(2, lw);
}
inline std::string VL_CVT_PACK_STR_NN(const std::string& lhs) VL_PURE {
    return lhs;
}
inline std::string VL_CVT_PACK_STR_NI(IData lhs) VL_PURE {
    WData lw[1];  lw[0] = lhs;
    return VL_CVT_PACK_STR_NW(1, lw);
}
inline std::string VL_CONCATN_NNN(const std::string& lhs, const std::string& rhs) VL_PURE {
    return lhs+rhs;
}
inline std::string VL_REPLICATEN_NNQ(int,int,int, const std::string& lhs, IData rep) VL_PURE {
    std::string out; out.reserve(lhs.length() * rep);
    for (unsigned times=0; times<rep; ++times) out += lhs;
    return out;
}
inline std::string VL_REPLICATEN_NNI(int obits,int lbits,int rbits,
                                     const std::string& lhs, IData rep) VL_PURE {
    return VL_REPLICATEN_NNQ(obits,lbits,rbits,lhs,rep);
}

inline IData VL_LEN_IN(const std::string& ld) { return ld.length(); }

extern IData VL_FOPEN_NI(const std::string& filename, IData mode) VL_MT_SAFE;
extern void VL_READMEM_N(bool hex, int width, int depth, int array_lsb,
                         const std::string& filename,
                         void* memp, IData start, IData end) VL_MT_SAFE;
extern void VL_WRITEMEM_N(bool hex, int width, int depth, int array_lsb,
                          const std::string& filename,
                          const void* memp, IData start, IData end) VL_MT_SAFE;
extern IData VL_SSCANF_INX(int lbits, const std::string& ld, const char* formatp, ...) VL_MT_SAFE;
extern void VL_SFORMAT_X(int obits_ignored, std::string& output, const char* formatp, ...) VL_MT_SAFE;
extern std::string VL_SFORMATF_NX(const char* formatp, ...) VL_MT_SAFE;
extern IData VL_VALUEPLUSARGS_INW(int rbits, const std::string& ld, WDataOutP rwp) VL_MT_SAFE;
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, IData& rdr) VL_MT_SAFE {
    WData rwp[2];  // WData must always be at least 2
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INQ(int rbits, const std::string& ld, QData& rdr) VL_MT_SAFE {
    WData rwp[2];
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = VL_SET_QW(rwp);
    return got;
}
extern IData VL_VALUEPLUSARGS_INN(int, const std::string& ld, std::string& rdr) VL_MT_SAFE;

#endif  // Guard
