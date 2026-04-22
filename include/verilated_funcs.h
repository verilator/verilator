// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated common functions
///
/// verilated.h should be included instead of this file.
///
/// Those macro/function/variable starting or ending in _ are internal,
/// however many of the other function/macros here are also internal.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_FUNCS_H_
#define VERILATOR_VERILATED_FUNCS_H_

#ifndef VERILATOR_VERILATED_H_INTERNAL_
#error "verilated_funcs.h should only be included by verilated.h"
#endif

#include <initializer_list>
#include <string>

//=========================================================================
// Extern functions -- User may override -- See verilated.cpp

/// Routine to call for $finish
/// User code may wish to replace this function, to do so, define VL_USER_FINISH.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_FINISH_MT instead, which eventually calls this.
extern void vl_finish(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE;

/// Routine to call for $stop and non-fatal error
/// User code may wish to replace this function, to do so, define VL_USER_STOP.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_STOP_MT instead, which eventually calls this.
extern void vl_stop(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE;

/// Routine to call for fatal messages
/// User code may wish to replace this function, to do so, define VL_USER_FATAL.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_FATAL_MT instead, which eventually calls this.
extern void vl_fatal(const char* filename, int linenum, const char* hier,
                     const char* msg) VL_MT_UNSAFE;

/// Routine to call for warning messages
/// User code may wish to replace this function, to do so, define VL_USER_WARN.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_WARN_MT instead, which eventually calls this.
extern void vl_warn(const char* filename, int linenum, const char* hier,
                    const char* msg) VL_MT_UNSAFE;

//=========================================================================
// Generator helpers

// clang-format off
#define VL_GEN_HELPER_ONE_ARG(macro) \
    macro(T) \
    macro(V) \
    macro(X)

#define VL_GEN_HELPER_TWO_ARG(macro) \
    macro(T, T) \
    macro(T, V) \
    macro(T, X) \
    macro(V, T) \
    macro(V, V) \
    macro(V, X) \
    macro(X, T) \
    macro(X, V) \
    macro(X, X)

#define VL_GEN_HELPER_THREE_ARG(macro) \
    macro(T, T, T) \
    macro(T, T, V) \
    macro(T, T, X) \
    macro(T, V, T) \
    macro(T, V, V) \
    macro(T, V, X) \
    macro(T, X, T) \
    macro(T, X, V) \
    macro(T, X, X) \
    macro(V, T, T) \
    macro(V, T, V) \
    macro(V, T, X) \
    macro(V, V, T) \
    macro(V, V, V) \
    macro(V, V, X) \
    macro(V, X, T) \
    macro(V, X, V) \
    macro(V, X, X) \
    macro(X, T, T) \
    macro(X, T, V) \
    macro(X, T, X) \
    macro(X, V, T) \
    macro(X, V, V) \
    macro(X, V, X) \
    macro(X, X, T) \
    macro(X, X, V) \
    macro(X, X, X)
// clang-format on

#define VL_TYPE_OFFSET_T (0)
#define VL_TYPE_OFFSET_V (0)
#define VL_TYPE_OFFSET_X (1)
#define VL_GET_TYPE_OFFSET(c) (VL_TYPE_OFFSET_##c)
#define VL_TYPE_JUMP_T (1)
#define VL_TYPE_JUMP_V (2)
#define VL_TYPE_JUMP_X (2)
#define VL_GET_TYPE_JUMP(c) (VL_TYPE_JUMP_##c)
// This is suboptimal since it calculates position everytime - we shall preferably just move
// pointers
#define VL_GET_ELEM(suffix, val, idx) \
    ((val) + static_cast<int>(VL_GET_TYPE_OFFSET(suffix) + ((idx) * VL_GET_TYPE_JUMP(suffix))))
#define VL_IF_VX_HELPER_T(stmt) \
    do { \
    } while (false);
#define VL_IF_VX_HELPER_V(stmt) \
    do { stmt } while (false);
#define VL_IF_VX_HELPER_X(stmt) \
    do { stmt } while (false);
#define VL_IF_VX(suffix, stmt) VL_IF_VX_HELPER_##suffix(stmt)
#define VL_IF_T_HELPER_T(stmt) \
    do { stmt } while (false);
#define VL_IF_T_HELPER_V(stmt) \
    do { \
    } while (false);
#define VL_IF_T_HELPER_X(stmt) \
    do { \
    } while (false);
#define VL_IF_T(suffix, stmt) VL_IF_T_HELPER_##suffix(stmt)

//=========================================================================
// Extern functions -- Slow path

/// Multithread safe wrapper for calls to $finish
extern void VL_FINISH_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE;
/// Multithread safe wrapper for calls to $stop
extern void VL_STOP_MT(const char* filename, int linenum, const char* hier,
                       bool maybe = true) VL_MT_SAFE;
/// Multithread safe wrapper to call for fatal messages
extern void VL_FATAL_MT(const char* filename, int linenum, const char* hier,
                        const char* msg) VL_MT_SAFE;
/// Multithread safe wrapper to call for warning messages
extern void VL_WARN_MT(const char* filename, int linenum, const char* hier,
                       const char* msg) VL_MT_SAFE;

/// Print a string, multithread safe. Eventually VL_PRINTF will get called.
extern void VL_PRINTF_MT(const char* formatp, ...) VL_ATTR_PRINTF(1) VL_MT_SAFE;

/// Print a debug message from internals with standard prefix, with printf style format
extern void VL_DBG_MSGF(const char* formatp, ...) VL_ATTR_PRINTF(1) VL_MT_SAFE;

/// Print a debug message from string via VL_DBG_MSGF
inline void VL_DBG_MSGS(const std::string& str) VL_MT_SAFE { VL_DBG_MSGF("%s", str.c_str()); }

/// Flush stdout
extern void VL_FFLUSH_MT() VL_MT_SAFE;

// EMIT_RULE: VL_RANDOM:  oclean=dirty
inline IData VL_RANDOM_I() VL_MT_SAFE { return vl_rand64(); }
inline QData VL_RANDOM_Q() VL_MT_SAFE { return vl_rand64(); }
extern WDataOutP VL_RANDOM_W(int obits, WDataOutP outwp) VL_MT_SAFE;
extern IData VL_RANDOM_SEEDED_II(IData& seedr) VL_MT_SAFE;
extern IData VL_URANDOM_SEEDED_II(IData seed) VL_MT_SAFE;
inline IData VL_URANDOM_RANGE_I(IData hi, IData lo) {
    const uint64_t rnd = vl_rand64();
    if (VL_LIKELY(hi > lo)) {
        // (hi - lo + 1) can be zero when hi is UINT_MAX and lo is zero
        if (VL_UNLIKELY(hi - lo + 1 == 0)) return rnd;
        // Modulus isn't very fast but it's common that hi-low is power-of-two
        return (rnd % (hi - lo + 1)) + lo;
    }
    if (VL_UNLIKELY(lo - hi + 1 == 0)) return rnd;
    return (rnd % (lo - hi + 1)) + hi;
}

// Random resets do not need four-state flavor since they are used to initialize x/z in two-state
// mode and x/z in four-state mode are just themselves

/// Random reset a signal of given width (init time only, var-specific PRNG)
extern IData VL_SCOPED_RAND_RESET_I(int obits, uint64_t scopeHash, uint64_t salt) VL_MT_UNSAFE;
/// Random reset a signal of given width (init time only, var-specific PRNG)
extern QData VL_SCOPED_RAND_RESET_Q(int obits, uint64_t scopeHash, uint64_t salt) VL_MT_UNSAFE;
/// Random reset a signal of given width (init time only, var-specific PRNG)
extern WDataOutP VL_SCOPED_RAND_RESET_W(int obits, WDataOutP outwp, uint64_t scopeHash,
                                        uint64_t salt) VL_MT_UNSAFE;

/// Random reset a signal of given width (assign time only)
extern IData VL_SCOPED_RAND_RESET_ASSIGN_I(int obits, uint64_t scopeHash,
                                           uint64_t salt) VL_MT_UNSAFE;
/// Random reset a signal of given width (assign time only)
extern QData VL_SCOPED_RAND_RESET_ASSIGN_Q(int obits, uint64_t scopeHash,
                                           uint64_t salt) VL_MT_UNSAFE;
/// Random reset a signal of given width (assign time only)
extern WDataOutP VL_SCOPED_RAND_RESET_ASSIGN_W(int obits, WDataOutP outwp, uint64_t scopeHash,
                                               uint64_t salt) VL_MT_UNSAFE;

/// Random reset a signal of given width (init time only)
extern IData VL_RAND_RESET_I(int obits) VL_MT_SAFE;
/// Random reset a signal of given width (init time only)
extern QData VL_RAND_RESET_Q(int obits) VL_MT_SAFE;
/// Random reset a signal of given width (init time only)
extern WDataOutP VL_RAND_RESET_W(int obits, WDataOutP outwp) VL_MT_SAFE;

/// Zero reset a signal (slow - else use VL_ZERO_W)
extern WDataOutP VL_ZERO_RESET_W_T(int obits, WDataOutP outwp) VL_MT_SAFE;
extern WDataOutP VL_ZERO_RESET_W_V(int obits, WDataOutP outwp) VL_MT_SAFE;
extern WDataOutP VL_ZERO_RESET_W_X(int obits, WDataOutP outwp) VL_MT_SAFE;
extern WDataOutP VL_ALLONES_RESET_W_T(int obits, WDataOutP outwp) VL_MT_SAFE;
extern WDataOutP VL_ALLONES_RESET_W_V(int obits, WDataOutP outwp) VL_MT_SAFE;
extern WDataOutP VL_ALLONES_RESET_W_X(int obits, WDataOutP outwp) VL_MT_SAFE;

extern void VL_PRINTTIMESCALE(const char* namep, const char* timeunitp,
                              const VerilatedContext* contextp) VL_MT_SAFE;

extern WDataOutP _vl_moddiv_w(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp,
                              bool is_modulus, int outputOffset, int outputJump, int lhsOffset,
                              int lhsJump, int rhsOffset, int rhsJump) VL_MT_SAFE;

extern void _vl_vsss_based(WDataOutP owp, int obits, int baseLog2, const char* strp,
                           size_t posstart, size_t posend) VL_MT_SAFE;

extern IData VL_FGETS_IXI(int obits, void* destp, IData fpi) VL_MT_SAFE;

extern void VL_FFLUSH_I(IData fdi) VL_MT_SAFE;
extern IData VL_FSEEK_I(IData fdi, IData offset, IData origin) VL_MT_SAFE;
extern IData VL_FTELL_I(IData fdi) VL_MT_SAFE;
extern void VL_FCLOSE_I(IData fdi) VL_MT_SAFE;

extern IData VL_FREAD_I(int width, int array_lsb, int array_size, void* memp, IData fpi,
                        IData start, IData count) VL_MT_SAFE;

extern IData VL_FSCANF_INX(IData fpi, const std::string& format, int argc, ...) VL_MT_SAFE;
extern IData VL_SSCANF_IINX(int lbits, IData ld, const std::string& format, int argc,
                            ...) VL_MT_SAFE;
extern IData VL_SSCANF_IQNX(int lbits, QData ld, const std::string& format, int argc,
                            ...) VL_MT_SAFE;
extern IData VL_SSCANF_IWNX(int lbits, WDataInP const lwp, const std::string& format, int argc,
                            ...) VL_MT_SAFE;

// String formatting functions taking const std::string& as format string
extern void VL_SFORMAT_NX(int obits, CData& destr, const std::string& format, int argc,
                          ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, SData& destr, const std::string& format, int argc,
                          ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, IData& destr, const std::string& format, int argc,
                          ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, QData& destr, const std::string& format, int argc,
                          ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, EData* destp, const std::string& format, int argc,
                          ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(std::string& output, const std::string& format, int argc,
                          ...) VL_MT_SAFE;
extern std::string VL_SFORMATF_N_NX(const std::string& format, int argc, ...) VL_MT_SAFE;
extern void VL_WRITEF_NX(const std::string& format, int argc, ...) VL_MT_SAFE;
extern void VL_FWRITEF_NX(IData fpi, const std::string& format, int argc, ...) VL_MT_SAFE;

// String formatting functions taking const char* format string
extern void VL_SFORMAT_NX(int obits, CData& destr, const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, SData& destr, const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, IData& destr, const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, QData& destr, const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(int obits, EData* destp, const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_SFORMAT_NX(std::string& output, const char* formatp, int argc, ...) VL_MT_SAFE;
extern std::string VL_SFORMATF_N_NX(const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_WRITEF_NX(const char* formatp, int argc, ...) VL_MT_SAFE;
extern void VL_FWRITEF_NX(IData fpi, const char* formatp, int argc, ...) VL_MT_SAFE;

extern void VL_STACKTRACE() VL_MT_SAFE;
extern std::string VL_STACKTRACE_N() VL_MT_SAFE;
extern IData VL_SYSTEM_IW(int lhswords, WDataInP const lhsp) VL_MT_SAFE;
extern IData VL_SYSTEM_IQ(QData lhs) VL_MT_SAFE;
inline IData VL_SYSTEM_II(IData lhs) VL_MT_SAFE { return VL_SYSTEM_IQ(lhs); }
extern IData VL_SYSTEM_IN(const std::string& lhs) VL_MT_SAFE;

extern IData VL_TESTPLUSARGS_I(const std::string& format) VL_MT_SAFE;
extern const char* vl_mc_scan_plusargs(const char* prefixp) VL_MT_SAFE;  // PLIish

//=========================================================================
// Base macros

// Return true if data[bit] set; not 0/1 return, but 0/non-zero return.
// Arguments must not have side effects
#define VL_BITISSETLIMIT_W(data, width, bit) (((bit) < (width)) && VL_BITISSET_W(data, bit))

// Shift appropriate word by bit. Does not account for wrapping between two words
// Argument 'bit' must not have side effects
#define VL_BITRSHIFT_W(data, bit) ((data)[VL_BITWORD_E(bit)] >> VL_BITBIT_E(bit))

// Create two 32-bit words from quadword
// WData is always at least 2 words; does not clean upper bits
#define VL_SET_WQ_T(owp, data) \
    do { \
        (owp)[0] = static_cast<IData>(data); \
        (owp)[1] = static_cast<IData>((data) >> VL_EDATASIZE); \
    } while (false)
#define VL_SET_WQ_V(owp, data) \
    do { \
        (owp)[VL_TYPE_OFFSET_V] = static_cast<IData>(data); \
        (owp)[VL_TYPE_OFFSET_V + VL_TYPE_JUMP_V] = static_cast<IData>((data) >> VL_EDATASIZE); \
    } while (false)
#define VL_SET_WQ_X(owp, data) \
    do { \
        (owp)[VL_TYPE_OFFSET_X] = static_cast<IData>(data); \
        (owp)[VL_TYPE_OFFSET_X + VL_TYPE_JUMP_X] = static_cast<IData>((data) >> VL_EDATASIZE); \
    } while (false)
#define VL_SET_WI(owp, data) \
    do { \
        (owp)[0] = static_cast<IData>(data); \
        (owp)[1] = 0; \
    } while (false)
#define VL_SET_QW(lwp) \
    ((static_cast<QData>((lwp)[0])) \
     | (static_cast<QData>((lwp)[1]) << (static_cast<QData>(VL_EDATASIZE))))
#define VL_SET_QII(ld, rd) ((static_cast<QData>(ld) << 32ULL) | static_cast<QData>(rd))

// Return FILE* from IData
extern FILE* VL_CVT_I_FP(IData lhs) VL_MT_SAFE;

// clang-format off
// Use a union to avoid cast-to-different-size warnings
// Return void* from QData
static inline void* VL_CVT_Q_VP(QData lhs) VL_PURE {
    union { void* fp; QData q; } u;
    u.q = lhs;
    return u.fp;
}
// Return QData from const void*
static inline QData VL_CVT_VP_Q(const void* fp) VL_PURE {
    union { const void* fp; QData q; } u;
    u.q = 0;
    u.fp = fp;
    return u.q;
}
// Return double from QData (bits, not numerically)
static inline double VL_CVT_D_Q(QData lhs) VL_PURE {
    union { double d; QData q; } u;
    u.q = lhs;
    return u.d;
}
// Return QData from double (bits, not numerically)
static inline QData VL_CVT_Q_D(double lhs) VL_PURE {
    union { double d; QData q; } u;
    u.d = lhs;
    return u.q;
}
// clang-format on
// Return string from DPI char*
static inline std::string VL_CVT_N_CSTR(const char* lhsp) VL_PURE {
    return lhsp ? std::string{lhsp} : ""s;
}

// Return queue from an unpacked array
template <typename T, std::size_t N_Depth>
static inline VlQueue<T> VL_CVT_UNPACK_TO_Q(const VlUnpacked<T, N_Depth>& q) VL_PURE {
    VlQueue<T> ret;
    for (size_t i = 0; i < N_Depth; ++i) ret.push_back(q[i]);
    return ret;
}

// Masked match functions
static inline IData VL_MATCHMASKED_I(int, IData lhs, WDataInP matchp) VL_PURE {
    size_t i = 0;
    while (true) {
        const IData mask = matchp[i * 2];
        const IData bits = matchp[i * 2 + 1];
        if ((mask & lhs) == bits) break;
        ++i;
    }
    return i;
}
static inline IData VL_MATCHMASKED_Q(int, QData lhs, WDataInP matchp) VL_PURE {
    size_t i = 0;
    while (true) {
        const QData mask = VL_SET_QW(matchp + i * 4);
        const QData bits = VL_SET_QW(matchp + i * 4 + 2);
        if ((mask & lhs) == bits) break;
        ++i;
    }
    return i;
}
static inline IData VL_MATCHMASKED_W(int lbits, WDataInP lhsp, WDataInP matchp) VL_MT_SAFE {
    const int iwords = VL_WORDS_I(lbits);
    size_t i = 0;
    while (true) {
        const WDataInP maskp = matchp + (i * iwords * 2);
        const WDataInP bitsp = matchp + (i * iwords * 2 + iwords);
        EData diff = 0;
        for (int j = 0; j < iwords; ++j) diff |= (maskp[j] & lhsp[j]) ^ bitsp[j];
        if (!diff) break;
        ++i;
    }
    return i;
}

// Return double from lhs (numeric) unsigned
double VL_ITOR_D_W(int lbits, WDataInP const lwp) VL_PURE;
static inline double VL_ITOR_D_I(int, IData lhs) VL_PURE {
    return static_cast<double>(static_cast<uint32_t>(lhs));
}
static inline double VL_ITOR_D_Q(int, QData lhs) VL_PURE {
    return static_cast<double>(static_cast<uint64_t>(lhs));
}
// Return double from lhs (numeric) signed
double VL_ISTOR_D_W(int lbits, WDataInP const lwp) VL_MT_SAFE;
static inline double VL_ISTOR_D_I(int lbits, IData lhs) VL_MT_SAFE {
    if (lbits == 32) return static_cast<double>(static_cast<int32_t>(lhs));
    VlWide<VL_WQ_WORDS_E> lwp;
    VL_SET_WI(lwp, lhs);
    return VL_ISTOR_D_W(lbits, lwp);
}
static inline double VL_ISTOR_D_Q(int lbits, QData lhs) VL_MT_SAFE {
    if (lbits == 64) return static_cast<double>(static_cast<int64_t>(lhs));
    VlWide<VL_WQ_WORDS_E> lwp;
    VL_SET_WQ_T(lwp, lhs);
    return VL_ISTOR_D_W(lbits, lwp);
}
// Return IData truncated from double (numeric)
static inline IData VL_RTOI_I_D(double lhs) VL_PURE { return static_cast<int32_t>(VL_TRUNC(lhs)); }

// Sign extend such that if MSB set, we get ffff_ffff, else 0s
// (Requires clean input)
#define VL_SIGN_I_T(nbits, lhs) ((lhs) >> VL_BITBIT_I((nbits) - VL_UL(1)))
#define VL_SIGN_Q_T(nbits, lhs) ((lhs) >> VL_BITBIT_Q((nbits) - 1ULL))
#define VL_SIGN_E_T(nbits, lhs) ((lhs) >> VL_BITBIT_E((nbits) - VL_EUL(1)))
#define VL_SIGN_W_T(nbits, rwp) \
    ((rwp)[VL_BITWORD_E((nbits) - VL_EUL(1))] >> VL_BITBIT_E((nbits) - VL_EUL(1)))
#define VL_SIGN_W_V(nbits, rwp) \
    ((rwp)[VL_BITWORD_E((nbits) - VL_EUL(1)) << 1] >> VL_BITBIT_E((nbits) - VL_EUL(1)))
#define VL_SIGN_W_X(nbits, rwp) \
    ((rwp)[(VL_BITWORD_E((nbits) - VL_EUL(1)) << 1) + 1] >> VL_BITBIT_E((nbits) - VL_EUL(1)))
#define VL_SIGNONES_E(nbits, lhs) (-(VL_SIGN_E_T(nbits, lhs)))

// Sign bit extended up to MSB, doesn't include unsigned portion
// Optimization bug in GCC 3.3 returns different bitmasks to later states for
static inline IData VL_EXTENDSIGN_I(int lbits, IData lhs) VL_PURE {
    return (-((lhs) & (VL_UL(1) << (lbits - 1))));
}
static inline QData VL_EXTENDSIGN_Q(int lbits, QData lhs) VL_PURE {
    return (-((lhs) & (1ULL << (lbits - 1))));
}

// Debugging prints
extern void _vl_debug_print_w(int lbits, WDataInP const iwp) VL_MT_SAFE;

//=========================================================================
// Time handling

// clang-format off

#ifdef SYSTEMC_VERSION
/// Return current simulation time
// Already defined: extern sc_time sc_time_stamp();
inline uint64_t vl_time_stamp64() VL_MT_SAFE { return sc_core::sc_time_stamp().value(); }
#else  // Non-SystemC
# if !defined(VL_TIME_CONTEXT) && !defined(VL_NO_LEGACY)
#  ifdef VL_TIME_STAMP64
// vl_time_stamp64() may be optionally defined by the user to return time.
// On MSVC++ weak symbols are not supported so must be declared, or define
// VL_TIME_CONTEXT.
extern uint64_t vl_time_stamp64() VL_ATTR_WEAK VL_MT_SAFE;
#  else
// sc_time_stamp() may be optionally defined by the user to return time.
// On MSVC++ weak symbols are not supported so must be declared, or define
// VL_TIME_CONTEXT.
extern double sc_time_stamp() VL_ATTR_WEAK VL_MT_SAFE;  // Verilator 4.032 and newer
inline uint64_t vl_time_stamp64() VL_MT_SAFE {
    // clang9.0.1 requires & although we really do want the weak symbol value
    // cppcheck-suppress duplicateValueTernary
    return VL_LIKELY(&sc_time_stamp) ? static_cast<uint64_t>(sc_time_stamp()) : 0;
}
#  endif
# endif
#endif

// clang-format on

uint64_t VerilatedContext::time() const VL_MT_SAFE {
    // When using non-default context, fastest path is return time
    if (VL_LIKELY(m_s.m_time)) return m_s.m_time;
#if defined(SYSTEMC_VERSION) || (!defined(VL_TIME_CONTEXT) && !defined(VL_NO_LEGACY))
    // Zero time could mean really at zero, or using callback
    // clang9.0.1 requires & although we really do want the weak symbol value
    if (VL_LIKELY(&vl_time_stamp64)) {  // else is weak symbol that is not defined
        return vl_time_stamp64();
    }
#endif
    return 0;
}

#define VL_TIME_Q() (Verilated::threadContextp()->time())
#define VL_TIME_D() (static_cast<double>(VL_TIME_Q()))

// Time scaled from 1-per-precision into a module's time units ("Unit"-ed, not "United")
// Optimized assuming scale is always constant.
// Can't use multiply in Q flavor, as might lose precision
#define VL_TIME_ROUND(t, p) (((t) + ((p) / 2)) / (p))
#define VL_TIME_UNITED_Q(scale) VL_TIME_ROUND(VL_TIME_Q(), static_cast<QData>(scale))
#define VL_TIME_UNITED_D(scale) (VL_TIME_D() / static_cast<double>(scale))

// Return time precision as multiplier of time units
double vl_time_multiplier(int scale) VL_PURE;
// Return power of 10. e.g. returns 100 if n==2
uint64_t vl_time_pow10(int n) VL_PURE;
// Return time as string with timescale suffix
std::string vl_timescaled_double(double value, const char* format = "%0.0f%s") VL_PURE;

//=========================================================================
// Functional macros/routines
// These all take the form
//      VL_func_IW(bits, bits, op, op)
//      VL_func_WW(bits, bits, out, op, op)
// The I/W indicates if it's a integer or wide for the output and each operand.
// The bits indicate the bit width of the output and each operand.
// If wide output, a temporary storage location is specified.

//===================================================================
// SETTING OPERATORS

VL_ATTR_ALWINLINE
static WDataOutP VL_MEMSET_ZERO_W(WDataOutP owp, int words) VL_MT_SAFE {
    std::memset(owp.datap(), 0, words * sizeof(EData));
    return owp;
}
VL_ATTR_ALWINLINE
static WDataOutP VL_MEMSET_ONES_W(WDataOutP owp, int words) VL_MT_SAFE {
    std::memset(owp.datap(), 0xff, words * sizeof(EData));
    return owp;
}
VL_ATTR_ALWINLINE
static WDataOutP VL_MEMCPY_W(WDataOutP owp, WDataInP const iwp, int words) VL_MT_SAFE {
    std::memcpy(owp.datap(), iwp.datap(), words * sizeof(EData));
    return owp;
}

// Output clean
// EMIT_RULE: VL_CLEAN:  oclean=clean; obits=lbits;
#define VL_CLEAN_II(obits, lbits, lhs) ((lhs) & (VL_MASK_I(obits)))
#define VL_CLEAN_QQ(obits, lbits, lhs) ((lhs) & (VL_MASK_Q(obits)))

// clang-format off
#define _vl_clean_inplace_w_GEN(outputSuffix) \
static inline WDataOutP _vl_clean_inplace_w_##outputSuffix(int obits, WDataOutP owp) \
        VL_MT_SAFE { \
        const int words = VL_WORDS_I(obits); \
        *VL_GET_ELEM(outputSuffix, owp, words - 1) &= VL_MASK_E(obits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(_vl_clean_inplace_w_GEN)
#undef _vl_clean_inplace_w_GEN

static inline WDataOutP VL_ZERO_W_T(int obits, WDataOutP owp) VL_MT_SAFE {
    return VL_MEMSET_ZERO_W(owp, VL_WORDS_I(obits));
}

// clang-format off
#define VL_ZERO_W_GEN(outputSuffix) \
static inline WDataOutP VL_ZERO_W_##outputSuffix(int obits, WDataOutP owp) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
            /* VL_MEMSET_ZERO_W is used because it uses std::memset which is kind of special \
             * since if no read from memory written by std::memset occur std::memset may be \
             * optimized away */ \
            VL_MEMSET_ZERO_W(owp, 1); \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
        } \
        return resultp; \
    }
// clang-format on
VL_ZERO_W_GEN(V)
VL_ZERO_W_GEN(X)
#undef VL_ZERO_W_GEN

static inline WDataOutP VL_ALLONES_W_T(int obits, WDataOutP owp) VL_MT_SAFE {
    const int words = VL_WORDS_I(obits);
    if (words) VL_MEMSET_ONES_W(owp, words - 1);
    owp[words - 1] = VL_MASK_E(obits);
    return owp;
}

// clang-format off
#define VL_ALLONES_W_GEN(outputSuffix) \
static inline WDataOutP VL_ALLONES_W_##outputSuffix(int obits, WDataOutP owp) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        /* Note iteration starts from one not zero - but i is not used to access data so its \
         * fine, we just finish a bit earlier which is also fine since we set last word after the \
         * loop */ \
        for (int i = 1; i < VL_WORDS_I(obits); ++i) { \
            /* VL_MEMSET_ZERO_W is used because it uses std::memset which is kind of special \
             * since if no read from memory written by std::memset occur std::memset may be \
             * optimized away */ \
            VL_MEMSET_ONES_W(owp, 1); \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
        } \
        *owp = VL_MASK_E(obits); \
        return resultp; \
    }
// clang-format on
VL_ALLONES_W_GEN(V)
VL_ALLONES_W_GEN(X)
#undef VL_ALLONES_W_GEN

// EMIT_RULE: VL_ASSIGN:  oclean=rclean; obits==lbits;
// For now, we always have a clean rhs.
// Note: If a ASSIGN isn't clean, use VL_ASSIGNCLEAN instead to do the same thing.
static inline WDataOutP VL_ASSIGN_W_TT(int obits, WDataOutP owp, WDataInP const lwp) VL_MT_SAFE {
    return VL_MEMCPY_W(owp, lwp, VL_WORDS_I(obits));
}

// clang-format off
#define VL_ASSIGN_W_GEN(outputSuffix, inputSuffix) \
static inline  WDataOutP VL_ASSIGN_W_##outputSuffix##inputSuffix(int obits, WDataOutP owp, WDataInP lwp) \
        VL_MT_SAFE { \
        const WDataOutP result = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        lwp += VL_GET_TYPE_OFFSET(inputSuffix); \
        for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
            *owp = *lwp; \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
            lwp += VL_GET_TYPE_JUMP(inputSuffix); \
        } \
        return result; \
    }
// clang-format on

// T - two state value
// V - value part
// X - xz part
VL_ASSIGN_W_GEN(V, V)
VL_ASSIGN_W_GEN(V, X)
VL_ASSIGN_W_GEN(V, T)
VL_ASSIGN_W_GEN(X, V)
VL_ASSIGN_W_GEN(X, X)
VL_ASSIGN_W_GEN(X, T)
VL_ASSIGN_W_GEN(T, V)
VL_ASSIGN_W_GEN(T, X)
#undef VL_ASSIGN_W_GEN

// EMIT_RULE: VL_ASSIGNBIT:  rclean=clean;
static inline void VL_ASSIGNBIT_II(int bit, CData& lhsr, IData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_UL(1) << VL_BITBIT_I(bit))) | (rhs << VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_II(int bit, SData& lhsr, IData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_UL(1) << VL_BITBIT_I(bit))) | (rhs << VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_II(int bit, IData& lhsr, IData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_UL(1) << VL_BITBIT_I(bit))) | (rhs << VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_QI(int bit, QData& lhsr, QData rhs) VL_PURE {
    lhsr = ((lhsr & ~(1ULL << VL_BITBIT_Q(bit))) | (static_cast<QData>(rhs) << VL_BITBIT_Q(bit)));
}
static inline void VL_ASSIGNBIT_WI(int bit, WDataOutP owp, IData rhs) VL_MT_SAFE {
    const EData orig = owp[VL_BITWORD_E(bit)];
    owp[VL_BITWORD_E(bit)] = ((orig & ~(VL_EUL(1) << VL_BITBIT_E(bit)))
                              | (static_cast<EData>(rhs) << VL_BITBIT_E(bit)));
}
// Alternative form that is an instruction faster when rhs is constant one.
static inline void VL_ASSIGNBIT_IO(int bit, CData& lhsr) VL_PURE {
    lhsr = (lhsr | (VL_UL(1) << VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_IO(int bit, SData& lhsr) VL_PURE {
    lhsr = (lhsr | (VL_UL(1) << VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_IO(int bit, IData& lhsr) VL_PURE {
    lhsr = (lhsr | (VL_UL(1) << VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_QO(int bit, QData& lhsr) VL_PURE {
    lhsr = (lhsr | (1ULL << VL_BITBIT_Q(bit)));
}
static inline void VL_ASSIGNBIT_WO(int bit, WDataOutP owp) VL_MT_SAFE {
    const EData orig = owp[VL_BITWORD_E(bit)];
    owp[VL_BITWORD_E(bit)] = (orig | (VL_EUL(1) << VL_BITBIT_E(bit)));
}

//===================================================================
// SYSTEMC OPERATORS
// Copying verilog format to systemc integers, doubles, and bit vectors.
// Get a SystemC variable

#define VL_ASSIGN_DSD(obits, vvar, svar) \
    { (vvar) = (svar).read(); }
#define VL_ASSIGN_ISI(obits, vvar, svar) \
    { (vvar) = VL_CLEAN_II((obits), (obits), (svar).read()); }
#define VL_ASSIGN_QSQ(obits, vvar, svar) \
    { (vvar) = VL_CLEAN_QQ((obits), (obits), (svar).read()); }

#define VL_ASSIGN_ISW(obits, od, svar) \
    { (od) = ((svar).read().get_word(0)) & VL_MASK_I(obits); }
#define VL_ASSIGN_QSW(obits, od, svar) \
    { \
        (od) = ((static_cast<QData>((svar).read().get_word(1))) << VL_IDATASIZE \
                | (svar).read().get_word(0)) \
               & VL_MASK_Q(obits); \
    }
#define VL_ASSIGN_WSW(obits, owp, svar) \
    { \
        const int words = VL_WORDS_I(obits); \
        for (int i = 0; i < words; ++i) (owp)[i] = (svar).read().get_word(i); \
        (owp)[words - 1] &= VL_MASK_E(obits); \
    }

#define VL_ASSIGN_ISU(obits, vvar, svar) \
    { (vvar) = VL_CLEAN_II((obits), (obits), (svar).read().to_uint()); }
#define VL_ASSIGN_QSU(obits, vvar, svar) \
    { (vvar) = VL_CLEAN_QQ((obits), (obits), (svar).read().to_uint64()); }
#define VL_ASSIGN_ISB(obits, vvar, svar) \
    { (vvar) = VL_CLEAN_II((obits), (obits), (svar).read().to_uint()); }
#define VL_ASSIGN_QSB(obits, vvar, svar) \
    { (vvar) = VL_CLEAN_QQ((obits), (obits), (svar).read().to_uint64()); }
#define VL_ASSIGN_WSB(obits, owp, svar) \
    { \
        const int words = VL_WORDS_I(obits); \
        sc_dt::sc_biguint<(obits)> _butemp = (svar).read(); \
        uint32_t* chunkp = _butemp.get_raw(); \
        int32_t lsb = 0; \
        while (lsb < (obits) - BITS_PER_DIGIT) { \
            const uint32_t data = *chunkp; \
            ++chunkp; \
            _vl_insert_WI_T(owp, data, lsb + BITS_PER_DIGIT - 1, lsb); \
            lsb += BITS_PER_DIGIT; \
        } \
        if (lsb < (obits)) { \
            const uint32_t msb_data = *chunkp; \
            _vl_insert_WI_T(owp, msb_data, (obits) - 1, lsb); \
        } \
        (owp)[words - 1] &= VL_MASK_E(obits); \
    }

// Copying verilog format from systemc integers, doubles, and bit vectors.
// Set a SystemC variable

#define VL_ASSIGN_SDD(obits, svar, vvar) \
    { (svar).write(vvar); }
#define VL_ASSIGN_SII(obits, svar, vvar) \
    { (svar).write(vvar); }
#define VL_ASSIGN_SQQ(obits, svar, vvar) \
    { (svar).write(vvar); }

#define VL_ASSIGN_SWI(obits, svar, rd) \
    { \
        sc_dt::sc_bv<(obits)> _bvtemp; \
        _bvtemp.set_word(0, (rd)); \
        (svar).write(_bvtemp); \
    }
#define VL_ASSIGN_SWQ(obits, svar, rd) \
    { \
        sc_dt::sc_bv<(obits)> _bvtemp; \
        _bvtemp.set_word(0, static_cast<IData>(rd)); \
        _bvtemp.set_word(1, static_cast<IData>((rd) >> VL_IDATASIZE)); \
        (svar).write(_bvtemp); \
    }
#define VL_ASSIGN_SWW(obits, svar, rwp) \
    { \
        sc_dt::sc_bv<(obits)> _bvtemp; \
        for (int i = 0; i < VL_WORDS_I(obits); ++i) _bvtemp.set_word(i, (rwp)[i]); \
        (svar).write(_bvtemp); \
    }

#define VL_ASSIGN_SUI(obits, svar, rd) \
    { (svar).write(rd); }
#define VL_ASSIGN_SUQ(obits, svar, rd) \
    { (svar).write(rd); }
#define VL_ASSIGN_SBI(obits, svar, rd) \
    { (svar).write(rd); }
#define VL_ASSIGN_SBQ(obits, svar, rd) \
    { (svar).write(rd); }
#define VL_ASSIGN_SBW(obits, svar, rwp) \
    { \
        sc_dt::sc_biguint<(obits)> _butemp; \
        int32_t lsb = 0; \
        uint32_t* chunkp = _butemp.get_raw(); \
        while (lsb + BITS_PER_DIGIT < (obits)) { \
            static_assert(std::is_same<IData, EData>::value, "IData and EData mismatch"); \
            const uint32_t data \
                = VL_SEL_IWII_TTTT(lsb + BITS_PER_DIGIT + 1, rwp, lsb, BITS_PER_DIGIT); \
            *chunkp = data & VL_MASK_E(BITS_PER_DIGIT); \
            ++chunkp; \
            lsb += BITS_PER_DIGIT; \
        } \
        if (lsb < (obits)) { \
            const uint32_t msb_data = VL_SEL_IWII_TTTT((obits) + 1, rwp, lsb, (obits) - lsb); \
            *chunkp = msb_data & VL_MASK_E((obits) - lsb); \
        } \
        _butemp.set(0, rwp[0] & 1); /* force update the sign */ \
        (svar).write(_butemp); \
    }

#define VL_ZERO_OFFSET_W_T(obits, owp) VL_ZERO_W_T(obits, owp)
#define VL_ZERO_OFFSET_W_V(obits, owp) VL_ZERO_W_V(obits, owp)
#define VL_ZERO_OFFSET_W_X(obits, owp) VL_ZERO_W_V(obits, owp)
#define VL_ALLONES_OFFSET_W_T(obits, owp) VL_ALLONES_W_T(obits, owp)
#define VL_ALLONES_OFFSET_W_V(obits, owp) VL_ALLONES_W_V(obits, owp)
#define VL_ALLONES_OFFSET_W_X(obits, owp) VL_ALLONES_W_V(obits, owp)
// ^ it does the trick because VL_TYPE_OFFSET_T and VL_TYPE_OFFSET_V are 0
static_assert(VL_TYPE_OFFSET_T == 0 && VL_TYPE_OFFSET_V == 0,
              "The VL_TYPE_OFFSET_T/V is not zero so, VL_ZERO_OFFSET_W_* must be adjusted");

//===================================================================
// Extending sizes

// CAREFUL, we're width changing, so obits!=lbits

// Right must be clean because otherwise size increase would pick up bad bits
// EMIT_RULE: VL_EXTEND:  oclean=clean; rclean==clean;
#define VL_EXTEND_II_TT(obits, lbits, lhs) ((lhs))
#define VL_EXTEND_QI_TT(obits, lbits, lhs) (static_cast<QData>(lhs))
#define VL_EXTEND_QQ_TT(obits, lbits, lhs) ((lhs))

// clang-format off
#define VL_EXTEND_WI_GEN(outputSuffix) \
static inline WDataOutP VL_EXTEND_WI_##outputSuffix##T(int obits, int, WDataOutP owp, IData ld) \
        VL_MT_SAFE { \
        /* Note for extracts that obits != lbits */ \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        *owp = ld; \
        owp += VL_GET_TYPE_JUMP(outputSuffix); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_EDATASIZE, owp); \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_EXTEND_WI_GEN)
#undef VL_EXTEND_WI_GEN

// clang-format off
#define VL_EXTEND_WQ_GEN(outputSuffix) \
static inline WDataOutP VL_EXTEND_WQ_##outputSuffix##T(int obits, int, WDataOutP const owp, \
                                                           QData ld) VL_MT_SAFE { \
        VL_SET_WQ_##outputSuffix(owp, ld); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_QUADSIZE, \
                                        VL_GET_ELEM(outputSuffix, owp, VL_WQ_WORDS_E)); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_EXTEND_WQ_GEN)
#undef VL_EXTEND_WQ_GEN

// clang-format off
#define VL_EXTEND_WQ_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_EXTEND_WW_##outputSuffix##lhsSuffix( \
        int obits, int lbits, WDataOutP owp, WDataInP const lwp) VL_MT_SAFE { \
        const int lwords = VL_WORDS_I(lbits); \
        VL_PREFETCH_RD(lwp.datap()); \
        VL_ZERO_W_##outputSuffix((VL_WORDS_I(obits) - lwords) * VL_EDATASIZE, \
                                 VL_GET_ELEM(outputSuffix, owp, lwords)); \
        return VL_ASSIGN_W_##outputSuffix##lhsSuffix(lbits, owp, lwp); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_EXTEND_WQ_GEN)
#undef VL_EXTEND_WQ_GEN

// EMIT_RULE: VL_EXTENDS:  oclean=*dirty*; obits=lbits;
// Sign extension; output dirty
static inline IData VL_EXTENDS_II_TT(int, int lbits, IData lhs) VL_PURE {
    return VL_EXTENDSIGN_I(lbits, lhs) | lhs;
}
static inline QData VL_EXTENDS_QI_TT(int, int lbits, QData lhs /*Q_as_need_extended*/) VL_PURE {
    return VL_EXTENDSIGN_Q(lbits, lhs) | lhs;
}
static inline QData VL_EXTENDS_QQ_TT(int, int lbits, QData lhs) VL_PURE {
    return VL_EXTENDSIGN_Q(lbits, lhs) | lhs;
}

// clang-format off
#define VL_EXTENDS_WI_GEN(outputSuffix) \
static inline WDataOutP VL_EXTENDS_WI_##outputSuffix##T(int obits, int lbits, WDataOutP owp, \
                                                            IData ld) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        *owp = ld; \
        if (VL_SIGN_I_T(lbits, ld)) { \
            *owp |= ~VL_MASK_E(lbits); \
            VL_ALLONES_OFFSET_W_##outputSuffix(obits - VL_EDATASIZE, \
                                               owp + VL_GET_TYPE_JUMP(outputSuffix)); \
        } else { \
            VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_EDATASIZE, \
                                            owp + VL_GET_TYPE_JUMP(outputSuffix)); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_EXTENDS_WI_GEN)
#undef VL_EXTENDS_WI_GEN

// clang-format off
#define VL_EXTENDS_WQ_GEN(outputSuffix) \
static inline WDataOutP VL_EXTENDS_WQ_##outputSuffix##T(int obits, int lbits, WDataOutP owp, \
                                                            QData ld) VL_MT_SAFE { \
        VL_SET_WQ_##outputSuffix(owp, ld); \
        if (VL_SIGN_Q_T(lbits, ld)) { \
            *VL_GET_ELEM(outputSuffix, owp, 1) |= ~VL_MASK_E(lbits); \
            VL_ALLONES_OFFSET_W_##outputSuffix(obits - VL_QUADSIZE, \
                                               VL_GET_ELEM(outputSuffix, owp, VL_WQ_WORDS_E)); \
        } else { \
            VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_QUADSIZE, \
                                            VL_GET_ELEM(outputSuffix, owp, VL_WQ_WORDS_E)); \
        } \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_EXTENDS_WQ_GEN)
#undef VL_EXTENDS_WQ_GEN

// clang-format off
#define VL_EXTENDS_WW_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_EXTENDS_WW_##outputSuffix##lhsSuffix( \
        int obits, int lbits, WDataOutP const owp, WDataInP const lwp) VL_MT_SAFE { \
        const int lwords = VL_WORDS_I(lbits); \
        VL_PREFETCH_RD(lwp.datap()); \
        VL_ASSIGN_W_##outputSuffix##lhsSuffix(lbits, owp, lwp); \
        if (VL_SIGN_W_##lhsSuffix(lbits, lwp)) { \
            *VL_GET_ELEM(outputSuffix, owp, lwords - 1) |= ~VL_MASK_E(lbits); \
            VL_ALLONES_OFFSET_W_##outputSuffix((VL_WORDS_I(obits) - lwords) * VL_EDATASIZE, \
                                               VL_GET_ELEM(outputSuffix, owp, lwords)); \
        } else { \
            VL_ZERO_OFFSET_W_##outputSuffix((VL_WORDS_I(obits) - lwords) * VL_EDATASIZE, \
                                            VL_GET_ELEM(outputSuffix, owp, lwords)); \
        } \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_EXTENDS_WW_GEN)
#undef VL_EXTENDS_WW_GEN

//===================================================================
// REDUCTION OPERATORS

// EMIT_RULE: VL_REDAND:  oclean=clean; lclean==clean; obits=1;
#define VL_REDAND_I_T(lbits, lhs) ((lhs) == VL_MASK_I(lbits))
#define VL_REDAND_Q_T(lbits, lhs) ((lhs) == VL_MASK_Q(lbits))

// clang-format off
#define VL_REDAND_W_GEN(lhsSuffix) \
static inline IData VL_REDAND_W_##lhsSuffix(int lbits, WDataInP lwp) VL_PURE { \
        const int words = VL_WORDS_I(lbits); \
        lwp = lwp + VL_GET_TYPE_OFFSET(lhsSuffix); \
        EData combine = *lwp; \
        for (int i = 1; i < words - 1; ++i) { \
            lwp = lwp + VL_GET_TYPE_JUMP(lhsSuffix); \
            combine &= *lwp; \
        } \
        lwp = lwp + VL_GET_TYPE_JUMP(lhsSuffix); \
        combine &= ~VL_MASK_E(lbits) | *lwp; \
        /* cppcheck-suppress knownConditionTrueFalse */ \
        return ((~combine) == 0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_REDAND_W_GEN)
#undef VL_REDAND_W_GEN

// EMIT_RULE: VL_REDOR:  oclean=clean; lclean==clean; obits=1;
#define VL_REDOR_I_T(lhs) ((lhs) != 0)
#define VL_REDOR_Q_T(lhs) ((lhs) != 0)

// clang-format off
#define VL_REDOR_W_GEN(lhsSuffix) \
static inline IData VL_REDOR_W_##lhsSuffix(int words, WDataInP lwp) VL_PURE { \
        EData equal = 0; \
        lwp = lwp + VL_GET_TYPE_OFFSET(lhsSuffix); \
        for (int i = 0; i < words; ++i) { \
            equal |= *lwp; \
            lwp = lwp + VL_GET_TYPE_JUMP(lhsSuffix); \
        } \
        return (equal != 0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_REDOR_W_GEN)
#undef VL_REDOR_W_GEN

// EMIT_RULE: VL_REDXOR:  oclean=dirty; obits=1;
static inline IData VL_REDXOR_2(IData r) VL_PURE {
    // Experiments show VL_REDXOR_2 is faster than __builtin_parityl
    r = (r ^ (r >> 1));
    return r;
}
static inline IData VL_REDXOR_4(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r = (r ^ (r >> 1));
    r = (r ^ (r >> 2));
    return r;
#endif
}
static inline IData VL_REDXOR_8(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r = (r ^ (r >> 1));
    r = (r ^ (r >> 2));
    r = (r ^ (r >> 4));
    return r;
#endif
}
static inline IData VL_REDXOR_16(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r = (r ^ (r >> 1));
    r = (r ^ (r >> 2));
    r = (r ^ (r >> 4));
    r = (r ^ (r >> 8));
    return r;
#endif
}
static inline IData VL_REDXOR_32(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r = (r ^ (r >> 1));
    r = (r ^ (r >> 2));
    r = (r ^ (r >> 4));
    r = (r ^ (r >> 8));
    r = (r ^ (r >> 16));
    return r;
#endif
}
static inline IData VL_REDXOR_64(QData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityll(r);
#else
    r = (r ^ (r >> 1));
    r = (r ^ (r >> 2));
    r = (r ^ (r >> 4));
    r = (r ^ (r >> 8));
    r = (r ^ (r >> 16));
    r = (r ^ (r >> 32));
    return static_cast<IData>(r);
#endif
}

// clang-format off
#define VL_REDXOR_W_GEN(lhsSuffix) \
static inline IData VL_REDXOR_W_##lhsSuffix(int words, WDataInP lwp) VL_PURE { \
        lwp = lwp + VL_GET_TYPE_OFFSET(lhsSuffix); \
        EData r = *lwp; \
        for (int i = 1; i < words; ++i) { \
            lwp = lwp + VL_GET_TYPE_JUMP(lhsSuffix); \
            r ^= *lwp; \
        } \
        return VL_REDXOR_32(r); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_REDXOR_W_GEN)
#undef VL_REDXOR_W_GEN

// EMIT_RULE: VL_COUNTONES_II:  oclean = false; lhs clean
static inline IData VL_COUNTONES_I(IData lhs) VL_PURE {
    // This is faster than __builtin_popcountl
    IData r = lhs - ((lhs >> 1) & 033333333333) - ((lhs >> 2) & 011111111111);
    r = (r + (r >> 3)) & 030707070707;
    r = (r + (r >> 6));
    r = (r + (r >> 12) + (r >> 24)) & 077;
    return r;
}
static inline IData VL_COUNTONES_Q(QData lhs) VL_PURE {
    return VL_COUNTONES_I(static_cast<IData>(lhs)) + VL_COUNTONES_I(static_cast<IData>(lhs >> 32));
}
#define VL_COUNTONES_E VL_COUNTONES_I
static inline IData VL_COUNTONES_W(int words, WDataInP const lwp) VL_PURE {
    EData r = 0;
    for (int i = 0; i < words; ++i) r += VL_COUNTONES_E(lwp[i]);
    return r;
}

// EMIT_RULE: VL_COUNTBITS_II:  oclean = false; lhs clean
static inline IData VL_COUNTBITS_I(int lbits, IData lhs, IData ctrl0, IData ctrl1,
                                   IData ctrl2) VL_PURE {
    const int ctrlSum = (ctrl0 & 0x1) + (ctrl1 & 0x1) + (ctrl2 & 0x1);
    if (ctrlSum == 3) return VL_COUNTONES_I(lhs);
    if (ctrlSum == 0) {
        const IData mask = (lbits == 32) ? -1 : ((1 << lbits) - 1);
        return VL_COUNTONES_I(~lhs & mask);
    }
    return (lbits == 32) ? 32 : lbits;
}
static inline IData VL_COUNTBITS_Q(int lbits, QData lhs, IData ctrl0, IData ctrl1,
                                   IData ctrl2) VL_PURE {
    return VL_COUNTBITS_I(32, static_cast<IData>(lhs), ctrl0, ctrl1, ctrl2)
           + VL_COUNTBITS_I(lbits - 32, static_cast<IData>(lhs >> 32), ctrl0, ctrl1, ctrl2);
}
#define VL_COUNTBITS_E VL_COUNTBITS_I
static inline IData VL_COUNTBITS_W(int lbits, int words, WDataInP const lwp, IData ctrl0,
                                   IData ctrl1, IData ctrl2) VL_MT_SAFE {
    EData r = 0;
    IData wordLbits = 32;
    for (int i = 0; i < words; ++i) {
        if (i == words - 1) wordLbits = VL_BITBIT_I(lbits);
        r += VL_COUNTBITS_E(wordLbits, lwp[i], ctrl0, ctrl1, ctrl2);
    }
    return r;
}

static inline IData VL_ONEHOT_I(IData lhs) VL_PURE {
    const IData y = lhs - 1;
    return y < (lhs ^ y);
}
static inline IData VL_ONEHOT_Q(QData lhs) VL_PURE {
    const QData y = lhs - 1;
    return y < (lhs ^ y);
}
static inline IData VL_ONEHOT_W(int words, WDataInP const lwp) VL_PURE {
    EData one = 0;
    for (int i = 0; (i < words); ++i) {
        if (lwp[i]) {
            if (one) return 0;
            one = 1;
            if (lwp[i] & (lwp[i] - 1)) return 0;
        }
    }
    return one;
}

static inline IData VL_ONEHOT0_I(IData lhs) VL_PURE { return ((lhs & (lhs - 1)) == 0); }
static inline IData VL_ONEHOT0_Q(QData lhs) VL_PURE { return ((lhs & (lhs - 1)) == 0); }
static inline IData VL_ONEHOT0_W(int words, WDataInP const lwp) VL_PURE {
    bool one = false;
    for (int i = 0; (i < words); ++i) {
        if (lwp[i]) {
            if (one) return 0;
            one = true;
            if (lwp[i] & (lwp[i] - 1)) return 0;
        }
    }
    return 1;
}

static inline IData VL_CLOG2_I(IData lhs) VL_PURE {
    // There are faster algorithms, or fls GCC4 builtins, but rarely used
    // In C++20 there will be std::bit_width(lhs) - 1
    if (VL_UNLIKELY(!lhs)) return 0;
    --lhs;
    int shifts = 0;
    for (; lhs != 0; ++shifts) lhs = lhs >> 1;
    return shifts;
}
static inline IData VL_CLOG2_Q(QData lhs) VL_PURE {
    if (VL_UNLIKELY(!lhs)) return 0;
    --lhs;
    int shifts = 0;
    for (; lhs != 0; ++shifts) lhs = lhs >> 1ULL;
    return shifts;
}
static inline IData VL_CLOG2_W(int words, WDataInP const lwp) VL_PURE {
    const EData adjust = (VL_COUNTONES_W(words, lwp) == 1) ? 0 : 1;
    for (int i = words - 1; i >= 0; --i) {
        if (VL_UNLIKELY(lwp[i])) {  // Shorter worst case if predict not taken
            for (int bit = VL_EDATASIZE - 1; bit >= 0; --bit) {
                if (VL_UNLIKELY(VL_BITISSET_E(lwp[i], bit))) {
                    return i * VL_EDATASIZE + bit + adjust;
                }
            }
            // Can't get here - one bit must be set
        }
    }
    return 0;
}

static inline IData VL_MOSTSETBITP1_I_T(IData lhs) VL_PURE {
    if (VL_UNLIKELY(!lhs)) return 0;  // __builtin_clz is undefined for 0
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return VL_EDATASIZE - __builtin_clz(lhs);
#else
    for (int bit = VL_EDATASIZE - 1; bit >= 0; --bit) {
        if (VL_BITISSET_E(lhs, bit)) return bit + 1;
    }
    return 0;  // LCOV_EXCL_LINE  // Can't get here - one bit must be set
#endif
}
static inline IData VL_MOSTSETBITP1_Q_T(QData lhs) VL_PURE {
    if (VL_UNLIKELY(!lhs)) return 0;
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return 64 - __builtin_clzll(static_cast<unsigned long long>(lhs));
#else
    const IData hi = static_cast<IData>(lhs >> 32ULL);
    return hi ? (VL_EDATASIZE + VL_MOSTSETBITP1_I_T(hi))
              : VL_MOSTSETBITP1_I_T(static_cast<IData>(lhs));
#endif
}

// clang-format off
#define VL_MOSTSETBITP1_W_GEN(suffix) \
static inline IData VL_MOSTSETBITP1_W_##suffix(int words, WDataInP lwp) VL_PURE { \
        lwp = lwp + VL_GET_TYPE_OFFSET(suffix) + ((words << ((VL_GET_TYPE_JUMP(suffix)) - 1)) - (VL_GET_TYPE_JUMP(suffix))); \
        /* MSB set bit plus one; similar to FLS.  0=value is zero */ \
        for (int i = words - 1; i >= 0; --i) { \
            /* Shorter worst case if predict not taken */ \
            if (VL_UNLIKELY(*lwp)) return i * VL_EDATASIZE + VL_MOSTSETBITP1_I_T(*lwp); \
            lwp = lwp - (VL_GET_TYPE_JUMP(suffix)); \
        } \
        return 0; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_MOSTSETBITP1_W_GEN)
#undef VL_MOSTSETBITP1_W_GEN

//===================================================================
// SIMPLE LOGICAL OPERATORS

// clang-format off
#define VL_BIOP_GEN(name, op, outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_##name##_W_##outputSuffix##lhsSuffix##rhsSuffix(int words, WDataOutP owp, WDataInP lwp, \
                                               WDataInP rwp) VL_MT_SAFE { \
    const WDataOutP result = owp; \
    owp += VL_GET_TYPE_OFFSET(outputSuffix); \
    lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
    rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
    for (int i = 0; (i < words); ++i) { \
        *owp = (*lwp op * rwp); \
        owp += VL_GET_TYPE_JUMP(outputSuffix); \
        lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
    } \
    return result; \
}
// clang-format on

// EMIT_RULE: VL_AND:  oclean=lclean||rclean; obits=lbits; lbits==rbits;
#define VL_AND_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
    VL_BIOP_GEN(AND, &, outputSuffix, lhsSuffix, rhsSuffix)
VL_GEN_HELPER_THREE_ARG(VL_AND_GEN)
#undef VL_AND_GEN
// EMIT_RULE: VL_OR:   oclean=lclean&&rclean; obits=lbits; lbits==rbits;
#define VL_OR_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
    VL_BIOP_GEN(OR, |, outputSuffix, lhsSuffix, rhsSuffix)
VL_GEN_HELPER_THREE_ARG(VL_OR_GEN)
#undef VL_OR_GEN
// EMIT_RULE: VL_XOR:  oclean=lclean&&rclean; obits=lbits; lbits==rbits;
#define VL_XOR_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
    VL_BIOP_GEN(XOR, ^, outputSuffix, lhsSuffix, rhsSuffix)
VL_GEN_HELPER_THREE_ARG(VL_XOR_GEN)
#undef VL_XOR_GEN

#undef VL_BIOP_GEN

// EMIT_RULE: VL_CHANGEXOR:  oclean=1; obits=32; lbits==rbits;
static inline IData VL_CHANGEXOR_W(int words, WDataInP const lwp, WDataInP const rwp) VL_PURE {
    IData od = 0;
    for (int i = 0; (i < words); ++i) od |= (lwp[i] ^ rwp[i]);
    return od;
}
// EMIT_RULE: VL_NOT:  oclean=dirty; obits=lbits;

// clang-format off

#define VL_NOT_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_NOT_W_##outputSuffix##lhsSuffix(int words, WDataOutP owp, WDataInP lwp) \
        VL_MT_SAFE { \
        const WDataOutP result = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
        for (int i = 0; i < words; ++i) { \
            *owp = ~(*lwp); \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
            lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
        } \
        return result; \
    }

// clang-format on

VL_GEN_HELPER_TWO_ARG(VL_NOT_GEN)
#undef VL_NOT_GEN

//=========================================================================
// Logical comparisons

// EMIT_RULE: VL_EQ:  oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_NEQ: oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_LT:  oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_GT:  oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_GTE: oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_LTE: oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
#define VL_LT_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) < 0)
#define VL_LT_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) < 0)
#define VL_LT_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) < 0)
#define VL_LT_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) < 0)
#define VL_LT_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) < 0)
#define VL_LT_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) < 0)
#define VL_LT_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) < 0)
#define VL_LT_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) < 0)
#define VL_LT_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) < 0)
#define VL_LT_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) < 0)
#define VL_LT_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) < 0)
#define VL_LT_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) < 0)
#define VL_LT_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) < 0)
#define VL_LT_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) < 0)
#define VL_LT_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) < 0)
#define VL_LT_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) < 0)
#define VL_LT_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) < 0)
#define VL_LT_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) < 0)
#define VL_LTE_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) <= 0)
#define VL_LTE_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) <= 0)
#define VL_LTE_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) <= 0)
#define VL_LTE_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) <= 0)
#define VL_LTE_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) <= 0)
#define VL_LTE_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) <= 0)
#define VL_LTE_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) <= 0)
#define VL_LTE_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) <= 0)
#define VL_LTE_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) <= 0)
#define VL_LTE_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) <= 0)
#define VL_LTE_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) <= 0)
#define VL_LTE_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) <= 0)
#define VL_LTE_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) <= 0)
#define VL_LTE_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) <= 0)
#define VL_LTE_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) <= 0)
#define VL_LTE_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) <= 0)
#define VL_LTE_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) <= 0)
#define VL_LTE_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) <= 0)
#define VL_GT_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) > 0)
#define VL_GT_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) > 0)
#define VL_GT_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) > 0)
#define VL_GT_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) > 0)
#define VL_GT_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) > 0)
#define VL_GT_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) > 0)
#define VL_GT_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) > 0)
#define VL_GT_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) > 0)
#define VL_GT_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) > 0)
#define VL_GT_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) > 0)
#define VL_GT_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) > 0)
#define VL_GT_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) > 0)
#define VL_GT_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) > 0)
#define VL_GT_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) > 0)
#define VL_GT_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) > 0)
#define VL_GT_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) > 0)
#define VL_GT_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) > 0)
#define VL_GT_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) > 0)
#define VL_GTE_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) >= 0)
#define VL_GTE_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) >= 0)
#define VL_GTE_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) >= 0)
#define VL_GTE_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) >= 0)
#define VL_GTE_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) >= 0)
#define VL_GTE_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) >= 0)
#define VL_GTE_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) >= 0)
#define VL_GTE_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) >= 0)
#define VL_GTE_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) >= 0)
#define VL_GTE_W_TT(words, lwp, rwp) (_vl_cmp_w_TT(words, lwp, rwp) >= 0)
#define VL_GTE_W_TV(words, lwp, rwp) (_vl_cmp_w_TV(words, lwp, rwp) >= 0)
#define VL_GTE_W_TX(words, lwp, rwp) (_vl_cmp_w_TX(words, lwp, rwp) >= 0)
#define VL_GTE_W_VT(words, lwp, rwp) (_vl_cmp_w_VT(words, lwp, rwp) >= 0)
#define VL_GTE_W_VV(words, lwp, rwp) (_vl_cmp_w_VV(words, lwp, rwp) >= 0)
#define VL_GTE_W_VX(words, lwp, rwp) (_vl_cmp_w_VX(words, lwp, rwp) >= 0)
#define VL_GTE_W_XT(words, lwp, rwp) (_vl_cmp_w_XT(words, lwp, rwp) >= 0)
#define VL_GTE_W_XV(words, lwp, rwp) (_vl_cmp_w_XV(words, lwp, rwp) >= 0)
#define VL_GTE_W_XX(words, lwp, rwp) (_vl_cmp_w_XX(words, lwp, rwp) >= 0)

// clang-format off
// Output clean, <lhs> AND <rhs> MUST BE CLEAN
#define VL_EQ_W_GEN(lhsSuffix, rhsSuffix) \
static inline IData VL_EQ_W_##lhsSuffix##rhsSuffix(int words, WDataInP lwp, WDataInP rwp) VL_PURE { \
        lwp = lwp + VL_GET_TYPE_OFFSET(lhsSuffix); \
        rwp = rwp + VL_GET_TYPE_OFFSET(rhsSuffix); \
        EData nequal = 0; \
        for (int i = 0; (i < words); ++i) { \
            nequal |= (*lwp ^ *rwp); \
            lwp = lwp + VL_GET_TYPE_JUMP(lhsSuffix); \
            rwp = rwp + VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return (nequal == 0); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_EQ_W_GEN)
#undef VL_EQ_W_GEN

#define VL_NEQ_R_TT(words, q, rwp) (!VL_EQ_R_TT(words, q, rwp))
#define VL_NEQ_W_TT(words, lwp, rwp) (!VL_EQ_W_TT(words, lwp, rwp))
#define VL_NEQ_W_TV(words, lwp, rwp) (!VL_EQ_W_TV(words, lwp, rwp))
#define VL_NEQ_W_TX(words, lwp, rwp) (!VL_EQ_W_TX(words, lwp, rwp))
#define VL_NEQ_W_VT(words, lwp, rwp) (!VL_EQ_W_VT(words, lwp, rwp))
#define VL_NEQ_W_VV(words, lwp, rwp) (!VL_EQ_W_VV(words, lwp, rwp))
#define VL_NEQ_W_VX(words, lwp, rwp) (!VL_EQ_W_VX(words, lwp, rwp))
#define VL_NEQ_W_XT(words, lwp, rwp) (!VL_EQ_W_XT(words, lwp, rwp))
#define VL_NEQ_W_XV(words, lwp, rwp) (!VL_EQ_W_XV(words, lwp, rwp))
#define VL_NEQ_W_XX(words, lwp, rwp) (!VL_EQ_W_XX(words, lwp, rwp))
#define VL_NEQ_W_TT(words, lwp, rwp) (!VL_EQ_W_TT(words, lwp, rwp))
#define VL_NEQ_W_TV(words, lwp, rwp) (!VL_EQ_W_TV(words, lwp, rwp))
#define VL_NEQ_W_TX(words, lwp, rwp) (!VL_EQ_W_TX(words, lwp, rwp))
#define VL_NEQ_W_VT(words, lwp, rwp) (!VL_EQ_W_VT(words, lwp, rwp))
#define VL_NEQ_W_VV(words, lwp, rwp) (!VL_EQ_W_VV(words, lwp, rwp))
#define VL_NEQ_W_VX(words, lwp, rwp) (!VL_EQ_W_VX(words, lwp, rwp))
#define VL_NEQ_W_XT(words, lwp, rwp) (!VL_EQ_W_XT(words, lwp, rwp))
#define VL_NEQ_W_XV(words, lwp, rwp) (!VL_EQ_W_XV(words, lwp, rwp))
#define VL_NEQ_W_XX(words, lwp, rwp) (!VL_EQ_W_XX(words, lwp, rwp))

// clang-format off
#define VL_EQ_R_GEN(rhsSuffix) \
template <std::size_t N_Words> \
static inline IData VL_EQ_W_##rhsSuffix##T(int words, WDataInP const rwp, \
                                               const VlQueue<VlWide<N_Words>>& q) VL_PURE { \
        return VL_EQ_R_T##rhsSuffix(words, q, rwp); \
    } \
template <typename T> \
static inline IData VL_EQ_W_##rhsSuffix##T(int words, WDataInP const rwp, VlQueue<T> q) \
        VL_PURE { \
        return VL_EQ_R_T##rhsSuffix(words, q, rwp); \
    } \
template <typename T> \
static inline IData VL_EQ_R_T##rhsSuffix(int words, VlQueue<T> q, WDataInP rwp) VL_PURE { \
        EData nequal = 0; \
        const int wordsInQ = q.size() * sizeof(T) / sizeof(IData) - 1; \
        if (wordsInQ + 1 != words) return false; \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        if VL_CONSTEXPR_CXX17 (sizeof(T) == 1) { \
            IData temp = 0; \
            for (int i = 0; (i < wordsInQ + 1); ++i) { \
                temp |= static_cast<EData>(q.at((wordsInQ - i) * sizeof(IData) + 3)); \
                temp |= static_cast<EData>(q.at((wordsInQ - i) * sizeof(IData) + 2)) << 8; \
                temp |= static_cast<EData>(q.at((wordsInQ - i) * sizeof(IData) + 1)) << 16; \
                temp |= static_cast<EData>(q.at((wordsInQ - i) * sizeof(IData))) << 24; \
                nequal |= (temp ^ *rwp); \
                temp = 0; \
                rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
            } \
        } else if VL_CONSTEXPR_CXX17 (sizeof(T) == 2) { \
            IData temp = 0; \
            for (int i = 0; (i < wordsInQ + 1); ++i) { \
                temp |= q.at((wordsInQ - i) * sizeof(SData) + 1); \
                temp |= q.at((wordsInQ - i) * sizeof(SData)) << 16; \
                nequal |= (temp ^ *rwp); \
                temp = 0; \
                rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
            } \
        } else if VL_CONSTEXPR_CXX17 (sizeof(T) == 4) { \
            for (int i = 0; (i < wordsInQ + 1); ++i) { nequal |= (q.at(wordsInQ - i) ^ rwp[i]); } \
        } else if VL_CONSTEXPR_CXX17 (sizeof(T) == 8) { \
            int qSize = q.size() - 1; \
            for (int i = 0; (i < qSize); i += 2) { \
                nequal |= (static_cast<QData>(q.at(qSize - i)) ^ *rwp); \
                rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
                nequal |= (static_cast<QData>(q.at(qSize - i)) >> 32 ^ *rwp); \
                rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
            } \
        } \
        return (nequal == 0); \
    } \
template <std::size_t N_Words> \
static inline IData VL_EQ_R_T##rhsSuffix(int words, const VlQueue<VlWide<N_Words>>& q, \
                                             WDataInP rwp) VL_PURE { \
        EData nequal = 0; \
        const int wordsInQ = q.size() * N_Words; \
        if ((q.size() * N_Words) != words) { return false; } \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        for (int qIndex = q.size() - 1; qIndex >= 0; qIndex--) { \
            for (int wordInElement = 0; wordInElement < N_Words; wordInElement++) { \
                nequal |= (q.at(qIndex).at(wordInElement) ^ *rwp); \
                rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
            } \
        } \
        return (nequal == 0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_EQ_R_GEN)
#undef VL_EQ_R_GEN

// Internal usage
// clang-format off
#define _vl_cmp_w_GEN(lhsSuffix, rhsSuffix) \
static inline int _vl_cmp_w_##lhsSuffix##rhsSuffix(int words, WDataInP lwp, WDataInP rwp) VL_PURE { \
        int i = words - 1; \
        lwp = lwp + VL_GET_TYPE_OFFSET(lhsSuffix) + (i * VL_GET_TYPE_JUMP(lhsSuffix)); \
        rwp = rwp + VL_GET_TYPE_OFFSET(rhsSuffix) + (i * VL_GET_TYPE_JUMP(rhsSuffix)); \
        for (; i >= 0; --i) { \
            if (*lwp > *rwp) return 1; \
            if (*lwp < *rwp) return -1; \
            lwp = lwp - VL_GET_TYPE_JUMP(lhsSuffix); \
            rwp = rwp - VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return 0;  /* == */ \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(_vl_cmp_w_GEN)
#undef _vl_cmp_w_GEN

#define VL_LTS_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) < 0)
#define VL_LTS_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) < 0)
#define VL_LTES_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) <= 0)
#define VL_LTES_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) <= 0)
#define VL_GTS_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) > 0)
#define VL_GTS_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) > 0)
#define VL_GTES_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_TT(lbits, lwp, rwp) (_vl_cmps_w_TT(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_TV(lbits, lwp, rwp) (_vl_cmps_w_TV(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_TX(lbits, lwp, rwp) (_vl_cmps_w_TX(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_VT(lbits, lwp, rwp) (_vl_cmps_w_VT(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_VV(lbits, lwp, rwp) (_vl_cmps_w_VV(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_VX(lbits, lwp, rwp) (_vl_cmps_w_VX(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_XT(lbits, lwp, rwp) (_vl_cmps_w_XT(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_XV(lbits, lwp, rwp) (_vl_cmps_w_XV(lbits, lwp, rwp) >= 0)
#define VL_GTES_IWW_XX(lbits, lwp, rwp) (_vl_cmps_w_XX(lbits, lwp, rwp) >= 0)

static inline IData VL_GTS_III_TT(int lbits, IData lhs, IData rhs) VL_PURE {
    // For lbits==32, this becomes just a single instruction, otherwise ~5.
    // GCC 3.3.4 sign extension bugs on AMD64 architecture force us to use quad logic
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);  // Q for gcc
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);  // Q for gcc
    return lhs_signed > rhs_signed;
}
static inline IData VL_GTS_IQQ_TT(int lbits, QData lhs, QData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);
    return lhs_signed > rhs_signed;
}

static inline IData VL_GTES_III_TT(int lbits, IData lhs, IData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);  // Q for gcc
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);  // Q for gcc
    return lhs_signed >= rhs_signed;
}
static inline IData VL_GTES_IQQ_TT(int lbits, QData lhs, QData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);
    return lhs_signed >= rhs_signed;
}

static inline IData VL_LTS_III_TT(int lbits, IData lhs, IData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);  // Q for gcc
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);  // Q for gcc
    return lhs_signed < rhs_signed;
}
static inline IData VL_LTS_IQQ_TT(int lbits, QData lhs, QData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);
    return lhs_signed < rhs_signed;
}

static inline IData VL_LTES_III_TT(int lbits, IData lhs, IData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);  // Q for gcc
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);  // Q for gcc
    return lhs_signed <= rhs_signed;
}
static inline IData VL_LTES_IQQ_TT(int lbits, QData lhs, QData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);
    return lhs_signed <= rhs_signed;
}

// clang-format off
#define _vl_cmps_w_GEN(lhsSuffix, rhsSuffix) \
static inline int _vl_cmps_w_##lhsSuffix##rhsSuffix(int lbits, WDataInP lwp, WDataInP rwp) VL_PURE { \
        const int words = VL_WORDS_I(lbits); \
        int i = words - 1; \
        lwp = lwp + VL_GET_TYPE_OFFSET(lhsSuffix) + (i * VL_GET_TYPE_JUMP(lhsSuffix)); \
        rwp = rwp + VL_GET_TYPE_OFFSET(rhsSuffix) + (i * VL_GET_TYPE_JUMP(rhsSuffix)); \
        /* We need to flip sense if negative comparison */ \
        const EData lsign = VL_SIGN_E_T(lbits, *lwp); \
        const EData rsign = VL_SIGN_E_T(lbits, *rwp); \
        if (!lsign && rsign) return 1;  /* + > - */ \
        if (lsign && !rsign) return -1;  /* - < + */ \
        for (; i >= 0; --i) { \
            if (*lwp > *rwp) return 1; \
            if (*lwp < *rwp) return -1; \
            lwp = lwp - VL_GET_TYPE_JUMP(lhsSuffix); \
            rwp = rwp - VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return 0;  /* == */ \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(_vl_cmps_w_GEN)
#undef _vl_cmps_w_GEN

//=========================================================================
// Expressions

// Output NOT clean
// clang-format off
#define VL_NEGATE_W_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_NEGATE_W_##outputSuffix##lhsSuffix(int words, WDataOutP owp, WDataInP lwp) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
        EData carry = 1; \
        for (int i = 0; i < words; ++i) { \
            *owp = ~(*lwp) + carry; \
            carry = (*owp < ~(*lwp)); \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
            lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_NEGATE_W_GEN)
#undef VL_NEGATE_W_GEN

// clang-format off
#define VL_NEGATE_INPLACE_W_GEN(suffix) \
static inline void VL_NEGATE_INPLACE_W_##suffix(int words, WDataOutP owp_lwp) VL_MT_SAFE { \
        owp_lwp += VL_GET_TYPE_OFFSET(suffix); \
        EData carry = 1; \
        for (int i = 0; i < words; ++i) { \
            const EData word = ~(*owp_lwp) + carry; \
            carry = (word < ~(*owp_lwp)); \
            (*owp_lwp) = word; \
            owp_lwp += VL_GET_TYPE_JUMP(suffix); \
        } \
    }
// clang-format on

VL_GEN_HELPER_ONE_ARG(VL_NEGATE_INPLACE_W_GEN)
#undef VL_NEGATE_INPLACE_W_GEN

// EMIT_RULE: VL_MUL:    oclean=dirty; lclean==clean; rclean==clean;
// EMIT_RULE: VL_DIV:    oclean=dirty; lclean==clean; rclean==clean;
// EMIT_RULE: VL_MODDIV: oclean=dirty; lclean==clean; rclean==clean;
static inline IData VL_DIV_III_TTT(int /*lbits*/, IData lhs, IData rhs) {
    return (rhs == 0) ? 0 : lhs / rhs;
}
static inline QData VL_DIV_QQQ_TTT(int /*lbits*/, QData lhs, QData rhs) {
    return (rhs == 0) ? 0 : lhs / rhs;
}
#define VL_DIV_WWW_TTT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_TTV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_TTX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_TVT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_TVV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_TVX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_TXT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_TXV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_TXX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_VTT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_VTV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_VTX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_VVT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_VVV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_VVX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_VXT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_VXV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_VXX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_XTT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_XTV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_XTX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_XVT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_XVV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_XVX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_DIV_WWW_XXT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_DIV_WWW_XXV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_DIV_WWW_XXX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 0, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))

static inline IData VL_MODDIV_III_TTT(int /*lbits*/, IData lhs, IData rhs) {
    return (rhs == 0) ? 0 : lhs % rhs;
}
static inline QData VL_MODDIV_QQQ_TTT(int /*lbits*/, QData lhs, QData rhs) {
    return (rhs == 0) ? 0 : lhs % rhs;
}
#define VL_MODDIV_WWW_TTT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_TTV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_TTX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_TVT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_TVV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_TVX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_TXT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_TXV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_TXX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_VTT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_VTV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_VTX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_VVT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_VVV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_VVX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_VXT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_VXV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_VXX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_XTT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_XTV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_XTX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(T), VL_GET_TYPE_JUMP(T), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_XVT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_XVV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_XVX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(V), VL_GET_TYPE_JUMP(V), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))
#define VL_MODDIV_WWW_XXT(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(T), \
                  VL_GET_TYPE_JUMP(T)))
#define VL_MODDIV_WWW_XXV(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(V), \
                  VL_GET_TYPE_JUMP(V)))
#define VL_MODDIV_WWW_XXX(lbits, owp, lwp, rwp) \
    (_vl_moddiv_w(lbits, owp, lwp, rwp, 1, VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), \
                  VL_GET_TYPE_OFFSET(X), VL_GET_TYPE_JUMP(X), VL_GET_TYPE_OFFSET(X), \
                  VL_GET_TYPE_JUMP(X)))

// clang-format off
#define VL_ADD_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_ADD_W_##outputSuffix##lhsSuffix##rhsSuffix(int words, WDataOutP owp, WDataInP lwp, \
                                            WDataInP rwp) VL_MT_SAFE { \
    const WDataOutP result = owp; \
    owp += VL_GET_TYPE_OFFSET(outputSuffix); \
    lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
    rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
    QData carry = 0; \
    for (int i = 0; i < words; ++i) { \
        carry = carry + static_cast<QData>(*lwp) + static_cast<QData>(*rwp); \
        *owp = (carry & 0xffffffffULL); \
        carry = (carry >> 32ULL) & 0xffffffffULL; \
        owp += VL_GET_TYPE_JUMP(outputSuffix); \
        lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
    } \
    /* Last output word is dirty */ \
    return result; \
}
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_ADD_GEN)
#undef VL_ADD_GEN

// clang-format off
#define VL_SUB_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_SUB_W_##outputSuffix##lhsSuffix##rhsSuffix(int words, WDataOutP owp, WDataInP lwp, \
                                            WDataInP rwp) VL_MT_SAFE { \
    const WDataOutP result = owp; \
    owp += VL_GET_TYPE_OFFSET(outputSuffix); \
    lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
    rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
    QData carry = 0; \
    for (int i = 0; i < words; ++i) { \
        carry = (carry + static_cast<QData>(*lwp) \
                    + static_cast<QData>(static_cast<IData>(~*rwp))); \
        if (i == 0) ++carry; /* Negation of rwp */ \
        *owp = (carry & 0xffffffffULL); \
        carry = (carry >> 32ULL) & 0xffffffffULL; \
        owp += VL_GET_TYPE_JUMP(outputSuffix); \
        lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
    } \
    /* Last output word is dirty */ \
    return result; \
}
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_SUB_GEN)
#undef VL_SUB_GEN

// clang-format off
#define VL_MUL_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_MUL_W_##outputSuffix##lhsSuffix##rhsSuffix(int words, WDataOutP owp, WDataInP lwp, \
                                 WDataInP rwp) VL_MT_SAFE { \
    const WDataOutP result = owp; \
    owp += VL_GET_TYPE_OFFSET(outputSuffix); \
    lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
    rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
    for (int i = 0; i < words; ++i) { \
        *owp = 0; \
        owp += VL_GET_TYPE_JUMP(outputSuffix); \
    } \
    for (int lword = 0; lword < words; ++lword) { \
        WDataInP currentRwp = rwp; \
        for (int rword = 0; rword < words; ++rword) { \
            QData mul = static_cast<QData>(*lwp) * static_cast<QData>(*currentRwp); \
            int qword = lword + rword; \
            owp = result + VL_GET_TYPE_OFFSET(outputSuffix) + qword * VL_GET_TYPE_JUMP(outputSuffix); \
            for (; qword < words; ++qword) { \
                mul += static_cast<QData>(*owp); \
                *owp = (mul & 0xffffffffULL); \
                mul = (mul >> 32ULL) & 0xffffffffULL; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            currentRwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
    } \
    /* Last output word is dirty */ \
    return result; \
}
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_MUL_GEN)
#undef VL_MUL_GEN

static inline IData VL_MULS_III_TTT(int lbits, IData lhs, IData rhs) VL_PURE {
    const int32_t lhs_signed = VL_EXTENDS_II_TT(32, lbits, lhs);
    const int32_t rhs_signed = VL_EXTENDS_II_TT(32, lbits, rhs);
    return lhs_signed * rhs_signed;
}
static inline QData VL_MULS_QQQ_TTT(int lbits, QData lhs, QData rhs) VL_PURE {
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(64, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(64, lbits, rhs);
    return lhs_signed * rhs_signed;
}

// clang-format off
#define VL_MULS_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_MULS_WWW_##outputSuffix##lhsSuffix##rhsSuffix( \
        int lbits, WDataOutP owp, WDataInP const lwp, WDataInP const rwp) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        const int words = VL_WORDS_I(lbits); \
        VL_DEBUG_IFDEF(assert(words <= VL_MULS_MAX_WORDS);); \
        /* cppcheck-suppress variableScope */ \
        VlWide<VL_MULS_MAX_WORDS> lwstore; /* Fixed size, as MSVC++ doesn't allow [words] here */ \
        /* cppcheck-suppress variableScope */ \
        VlWide<VL_MULS_MAX_WORDS> rwstore; \
        WDataInP lwusp = lwp; \
        WDataInP rwusp = rwp; \
        const EData lneg = VL_SIGN_E_T(lbits, *VL_GET_ELEM(lhsSuffix, lwp, words - 1)); \
        if (lneg) { /* Negate lhs */ \
            lwusp = lwstore; \
            VL_NEGATE_W_T##lhsSuffix(words, lwstore, lwp); \
            lwstore[words - 1] &= VL_MASK_E(lbits); /* Clean it */ \
        } \
        const EData rneg = VL_SIGN_E_T(lbits, *VL_GET_ELEM(rhsSuffix, rwp, words - 1)); \
        if (rneg) { /* Negate rhs */ \
            rwusp = rwstore; \
            VL_NEGATE_W_T##rhsSuffix(words, rwstore, rwp); \
            rwstore[words - 1] &= VL_MASK_E(lbits); /* Clean it */ \
        } \
        if (rneg) { \
            if (lneg) { \
                VL_MUL_W_##outputSuffix##TT(words, owp, lwusp, rwusp); \
            } else { \
                VL_MUL_W_##outputSuffix##lhsSuffix##T(words, owp, lwusp, rwusp); \
            } \
        } else { \
            if (lneg) { \
                VL_MUL_W_##outputSuffix##T##rhsSuffix(words, owp, lwusp, rwusp); \
            } else { \
                VL_MUL_W_##outputSuffix##lhsSuffix##rhsSuffix(words, owp, lwusp, rwusp); \
            } \
        } \
        *VL_GET_ELEM(outputSuffix, owp, words - 1) &= VL_MASK_E( \
            lbits); /* Clean.  Note it's ok for the multiply to overflow into the sign bit */ \
        if ((lneg ^ rneg) & 1) { /* Negate output (not using NEGATE, as owp==lwp) */ \
            QData carry = 0; \
            owp += VL_GET_TYPE_OFFSET(outputSuffix); \
            for (int i = 0; i < words; ++i) { \
                carry = carry + static_cast<QData>(static_cast<IData>(~*owp)); \
                if (i == 0) ++carry; /* Negation of temp2 */ \
                *owp = (carry & 0xffffffffULL); \
                carry = (carry >> 32ULL) & 0xffffffffULL; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            /* Not needed: owp[words-1] |= 1<<VL_BITBIT_E(lbits-1); */ /* Set sign bit */ \
        } \
        /* Last output word is dirty */ \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_MULS_WWW_GEN)
#undef VL_MULS_WWW_GEN

static inline IData VL_DIVS_III_TTT(int lbits, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs == 0)) return 0;
    // -MAX / -1 cannot be represented in twos complement, and will cause SIGFPE
    if (VL_UNLIKELY(lhs == 0x80000000 && rhs == 0xffffffff)) return 0;
    const int32_t lhs_signed = VL_EXTENDS_II_TT(VL_IDATASIZE, lbits, lhs);
    const int32_t rhs_signed = VL_EXTENDS_II_TT(VL_IDATASIZE, lbits, rhs);
    return lhs_signed / rhs_signed;
}
static inline QData VL_DIVS_QQQ_TTT(int lbits, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs == 0)) return 0;
    // -MAX / -1 cannot be represented in twos complement, and will cause SIGFPE
    if (VL_UNLIKELY(lhs == 0x8000000000000000ULL && rhs == 0xffffffffffffffffULL)) return 0;
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(VL_QUADSIZE, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(VL_QUADSIZE, lbits, rhs);
    return lhs_signed / rhs_signed;
}
static inline IData VL_MODDIVS_III_TTT(int lbits, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs == 0)) return 0;
    if (VL_UNLIKELY(lhs == 0x80000000 && rhs == 0xffffffff)) return 0;
    const int32_t lhs_signed = VL_EXTENDS_II_TT(VL_IDATASIZE, lbits, lhs);
    const int32_t rhs_signed = VL_EXTENDS_II_TT(VL_IDATASIZE, lbits, rhs);
    return lhs_signed % rhs_signed;
}
static inline QData VL_MODDIVS_QQQ_TTT(int lbits, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs == 0)) return 0;
    if (VL_UNLIKELY(lhs == 0x8000000000000000ULL && rhs == 0xffffffffffffffffULL)) return 0;
    const int64_t lhs_signed = VL_EXTENDS_QQ_TT(VL_QUADSIZE, lbits, lhs);
    const int64_t rhs_signed = VL_EXTENDS_QQ_TT(VL_QUADSIZE, lbits, rhs);
    return lhs_signed % rhs_signed;
}

// clang-format off
#define VL_DIVS_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_DIVS_WWW_##outputSuffix##lhsSuffix##rhsSuffix( \
        int lbits, WDataOutP owp, WDataInP const lwp, WDataInP const rwp) VL_MT_SAFE { \
        const int lwords = VL_WORDS_I(lbits); \
        const EData lsign = VL_SIGN_E_T(lbits, *VL_GET_ELEM(lhsSuffix, lwp, lwords - 1)); \
        const EData rsign = VL_SIGN_E_T(lbits, *VL_GET_ELEM(rhsSuffix, rwp, lwords - 1)); \
        VL_DEBUG_IFDEF(assert(lwords <= VL_MULS_MAX_WORDS);); \
        /* cppcheck-suppress variableScope */ \
        VlWide<VL_MULS_MAX_WORDS> lwstore; /* Fixed size, as MSVC++ doesn't allow [words] here */ \
        /* cppcheck-suppress variableScope */ \
        VlWide<VL_MULS_MAX_WORDS> rwstore; \
        WDataInP ltup = lwp; \
        WDataInP rtup = rwp; \
        if (lsign) ltup = _vl_clean_inplace_w_T(lbits, VL_NEGATE_W_T##lhsSuffix(lwords, lwstore, lwp)); \
        if (rsign) rtup = _vl_clean_inplace_w_T(lbits, VL_NEGATE_W_T##rhsSuffix(lwords, rwstore, rwp)); \
        if ((lsign && !rsign) || (!lsign && rsign)) { \
            VlWide<VL_MULS_MAX_WORDS> qNoSign; \
            if (lsign && !rsign) { \
                VL_DIV_WWW_TT##rhsSuffix(lbits, qNoSign, ltup, rtup); \
            } else { \
                VL_DIV_WWW_T##lhsSuffix##T(lbits, qNoSign, ltup, rtup); \
            } \
            _vl_clean_inplace_w_##outputSuffix(lbits, VL_NEGATE_W_##outputSuffix##T(lwords, owp, qNoSign)); \
            return owp; \
        } \
        if (lsign /*&& rsign*/) return VL_DIV_WWW_##outputSuffix##TT(lbits, owp, ltup, rtup); \
        return VL_DIV_WWW_##outputSuffix##lhsSuffix##rhsSuffix(lbits, owp, ltup, rtup); \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_DIVS_WWW_GEN)
#undef VL_DIVS_WWW_GEN

// clang-format off
#define VL_MODDIVS_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_MODDIVS_WWW_##outputSuffix##lhsSuffix##rhsSuffix( \
        int lbits, WDataOutP owp, WDataInP const lwp, WDataInP const rwp) VL_MT_SAFE { \
        const int lwords = VL_WORDS_I(lbits); \
        const EData lsign = VL_SIGN_E_T(lbits, *VL_GET_ELEM(lhsSuffix, lwp, lwords - 1)); \
        const EData rsign = VL_SIGN_E_T(lbits, *VL_GET_ELEM(rhsSuffix, rwp, lwords - 1)); \
        VL_DEBUG_IFDEF(assert(lwords <= VL_MULS_MAX_WORDS);); \
        /* cppcheck-suppress variableScope */ \
        VlWide<VL_MULS_MAX_WORDS> lwstore; /* Fixed size, as MSVC++ doesn't allow [words] here */ \
        /* cppcheck-suppress variableScope */ \
        VlWide<VL_MULS_MAX_WORDS> rwstore; \
        WDataInP ltup = lwp; \
        WDataInP rtup = rwp; \
        if (lsign) ltup = _vl_clean_inplace_w_T(lbits, VL_NEGATE_W_T##lhsSuffix(lwords, lwstore, lwp)); \
        if (rsign) rtup = _vl_clean_inplace_w_T(lbits, VL_NEGATE_W_T##rhsSuffix(lwords, rwstore, rwp)); \
        if (lsign) { /* Only dividend sign matters for modulus */ \
            VlWide<VL_MULS_MAX_WORDS> qNoSign; \
            if (rsign) { \
                VL_MODDIV_WWW_TTT(lbits, qNoSign, ltup, rtup); \
            } else { \
                VL_MODDIV_WWW_TT##rhsSuffix(lbits, qNoSign, ltup, rtup); \
            } \
            _vl_clean_inplace_w_##outputSuffix(lbits, VL_NEGATE_W_##outputSuffix##T(lwords, owp, qNoSign)); \
            return owp; \
        } \
        if (rsign) return VL_MODDIV_WWW_##outputSuffix##lhsSuffix##T(lbits, owp, ltup, rtup); \
        return VL_MODDIV_WWW_##outputSuffix##lhsSuffix##rhsSuffix(lbits, owp, ltup, rtup); \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_MODDIVS_WWW_GEN)
#undef VL_MODDIVS_WWW_GEN

#define VL_POW_IIQ(obits, lbits, rbits, lhs, rhs) VL_POW_QQQ(obits, lbits, rbits, lhs, rhs)
#define VL_POW_IIW(obits, lbits, rbits, lhs, rwp) VL_POW_QQW(obits, lbits, rbits, lhs, rwp)
#define VL_POW_QQI(obits, lbits, rbits, lhs, rhs) VL_POW_QQQ(obits, lbits, rbits, lhs, rhs)
#define VL_POW_WWI(obits, lbits, rbits, owp, lwp, rhs) \
    VL_POW_WWQ(obits, lbits, rbits, owp, lwp, rhs)

static inline IData VL_POW_III(int, int, int rbits, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs == 0)) return 1;
    if (VL_UNLIKELY(lhs == 0)) return 0;
    IData power = lhs;
    IData out = 1;
    for (int i = 0; i < rbits; ++i) {
        if (i > 0) power = power * power;
        if (rhs & (1ULL << i)) out *= power;
    }
    return out;
}
static inline QData VL_POW_QQQ(int, int, int rbits, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs == 0)) return 1;
    if (VL_UNLIKELY(lhs == 0)) return 0;
    QData power = lhs;
    QData out = 1ULL;
    for (int i = 0; i < rbits; ++i) {
        if (i > 0) power = power * power;
        if (rhs & (1ULL << i)) out *= power;
    }
    return out;
}
WDataOutP VL_POW_WWW(int obits, int, int rbits, WDataOutP owp, WDataInP const lwp,
                     WDataInP const rwp) VL_MT_SAFE;
WDataOutP VL_POW_WWQ(int obits, int, int rbits, WDataOutP owp, WDataInP const lwp,
                     QData rhs) VL_MT_SAFE;
QData VL_POW_QQW(int obits, int, int rbits, QData lhs, WDataInP const rwp) VL_MT_SAFE;

#define VL_POWSS_IIQ(obits, lbits, rbits, lhs, rhs, lsign, rsign) \
    VL_POWSS_QQQ(obits, lbits, rbits, lhs, rhs, lsign, rsign)
#define VL_POWSS_IIQ(obits, lbits, rbits, lhs, rhs, lsign, rsign) \
    VL_POWSS_QQQ(obits, lbits, rbits, lhs, rhs, lsign, rsign)
#define VL_POWSS_IIW(obits, lbits, rbits, lhs, rwp, lsign, rsign) \
    VL_POWSS_QQW(obits, lbits, rbits, lhs, rwp, lsign, rsign)
#define VL_POWSS_QQI(obits, lbits, rbits, lhs, rhs, lsign, rsign) \
    VL_POWSS_QQQ(obits, lbits, rbits, lhs, rhs, lsign, rsign)
#define VL_POWSS_WWI(obits, lbits, rbits, owp, lwp, rhs, lsign, rsign) \
    VL_POWSS_WWQ(obits, lbits, rbits, owp, lwp, rhs, lsign, rsign)

static inline IData VL_POWSS_III(int obits, int, int rbits, IData lhs, IData rhs, bool lsign,
                                 bool rsign) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs == 0)) return 1;
    if (rsign && VL_SIGN_I_T(rbits, rhs)) {
        if (lhs == 0) {
            return 0;  // "X"
        }
        if (lhs == 1) { return 1; }
        if (lsign && lhs == VL_MASK_I(obits)) {  // -1
            if (rhs & 1) return VL_MASK_I(obits);  // -1^odd=-1
            return 1;  // -1^even=1
        }
        return 0;
    }
    return VL_POW_III(obits, rbits, rbits, lhs, rhs);
}
static inline QData VL_POWSS_QQQ(int obits, int, int rbits, QData lhs, QData rhs, bool lsign,
                                 bool rsign) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs == 0)) return 1;
    if (rsign && VL_SIGN_Q_T(rbits, rhs)) {
        if (lhs == 0) return 0;  // "X"

        if (lhs == 1) return 1;
        if (lsign && lhs == VL_MASK_Q(obits)) {  // -1
            if (rhs & 1) return VL_MASK_Q(obits);  // -1^odd=-1
            return 1;  // -1^even=1
        }
        return 0;
    }
    return VL_POW_QQQ(obits, rbits, rbits, lhs, rhs);
}
WDataOutP VL_POWSS_WWW(int obits, int, int rbits, WDataOutP owp, WDataInP const lwp,
                       WDataInP const rwp, bool lsign, bool rsign) VL_MT_SAFE;
WDataOutP VL_POWSS_WWQ(int obits, int, int rbits, WDataOutP owp, WDataInP const lwp, QData rhs,
                       bool lsign, bool rsign) VL_MT_SAFE;
QData VL_POWSS_QQW(int obits, int, int rbits, QData lhs, WDataInP const rwp, bool lsign,
                   bool rsign) VL_MT_SAFE;

//===================================================================
// Concat/replication

// INTERNAL: Stuff LHS bit 0++ into OUTPUT at specified offset
// ld may be "dirty", output is clean
static inline void _vl_insert_II(CData& lhsr, IData ld, int hbit, int lbit, int rbits) VL_PURE {
    const IData cleanmask = VL_MASK_I(rbits);
    const IData insmask = (VL_MASK_I(hbit - lbit + 1)) << lbit;
    lhsr = (lhsr & ~insmask) | ((ld << lbit) & (insmask & cleanmask));
}
static inline void _vl_insert_II(SData& lhsr, IData ld, int hbit, int lbit, int rbits) VL_PURE {
    const IData cleanmask = VL_MASK_I(rbits);
    const IData insmask = (VL_MASK_I(hbit - lbit + 1)) << lbit;
    lhsr = (lhsr & ~insmask) | ((ld << lbit) & (insmask & cleanmask));
}
static inline void _vl_insert_II(IData& lhsr, IData ld, int hbit, int lbit, int rbits) VL_PURE {
    const IData cleanmask = VL_MASK_I(rbits);
    const IData insmask = (VL_MASK_I(hbit - lbit + 1)) << lbit;
    lhsr = (lhsr & ~insmask) | ((ld << lbit) & (insmask & cleanmask));
}
static inline void _vl_insert_QQ(QData& lhsr, QData ld, int hbit, int lbit, int rbits) VL_PURE {
    const QData cleanmask = VL_MASK_Q(rbits);
    const QData insmask = (VL_MASK_Q(hbit - lbit + 1)) << lbit;
    lhsr = (lhsr & ~insmask) | ((ld << lbit) & (insmask & cleanmask));
}
// clang-format off
#define _vl_insert_WI_GEN(outputSuffix) \
static inline void _vl_insert_WI_##outputSuffix(WDataOutP iowp, IData ld, int hbit, int lbit, \
                                                    int rbits = 0) VL_MT_SAFE { \
        /* Insert value ld into iowp at bit slice [hbit:lbit]. iowp is rbits wide. */ \
        const int hoffset = VL_BITBIT_E(hbit); \
        const int loffset = VL_BITBIT_E(lbit); \
        const int roffset = VL_BITBIT_E(rbits); \
        const int hword = VL_BITWORD_E(hbit); \
        const int lword = VL_BITWORD_E(lbit); \
        const int rword = VL_BITWORD_E(rbits); \
        const EData cleanmask = hword == rword ? VL_MASK_E(roffset) : VL_MASK_E(0); \
        if (hoffset == VL_SIZEBITS_E && loffset == 0) { \
            /* Fast and common case, word based insertion */ \
            *VL_GET_ELEM(outputSuffix, iowp, lword) = ld & cleanmask; \
        } else { \
            const EData lde = static_cast<EData>(ld); \
            if (hword == lword) { /* know < EData bits because above checks it */ \
                /* Assignment is contained within one word of destination */ \
                const EData insmask = (VL_MASK_E(hoffset - loffset + 1)) << loffset; \
                iowp = VL_GET_ELEM(outputSuffix, iowp, lword); \
                *iowp = (*iowp & ~insmask) | ((lde << loffset) & (insmask & cleanmask)); \
            } else { \
                /* Assignment crosses a word boundary in destination */ \
                const EData hinsmask = (VL_MASK_E(hoffset - 0 + 1)) << 0; \
                const EData linsmask = (VL_MASK_E((VL_EDATASIZE - 1) - loffset + 1)) << loffset; \
                const int nbitsonright = VL_EDATASIZE - loffset; /* bits that end up in lword */ \
                *VL_GET_ELEM(outputSuffix, iowp, lword) \
                    = (*VL_GET_ELEM(outputSuffix, iowp, lword) & ~linsmask) \
                      | ((lde << loffset) & linsmask); \
                /* Prevent unsafe write where lword was final writable location and hword is \
                   out-of-bounds. */ \
                if (VL_LIKELY(!(hword == rword && roffset == 0))) { \
                    iowp = VL_GET_ELEM(outputSuffix, iowp, hword); \
                    *iowp \
                        = (*iowp & ~hinsmask) | ((lde >> nbitsonright) & (hinsmask & cleanmask)); \
                } \
            } \
        } \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(_vl_insert_WI_GEN)
#undef _vl_insert_WI_GEN

// Copy bits from lwp[hbit:lbit] to low bits of lhsr. rbits is real width of lshr
// clang-format off
#define _vl_insert_IW_GEN(rhsSuffix) \
static inline void _vl_insert_IW_T##rhsSuffix(IData& lhsr, WDataInP const lwp, int hbit, \
                                                  int lbit, int rbits = 0) VL_MT_SAFE { \
        const int hoffset = VL_BITBIT_E(hbit); \
        const int loffset = VL_BITBIT_E(lbit); \
        const int hword = VL_BITWORD_E(hbit); \
        const int lword = VL_BITWORD_E(lbit); \
        const IData cleanmask = VL_MASK_I(rbits); \
        if (hword == lword) { \
            const IData insmask = (VL_MASK_I(hoffset - loffset + 1)); \
            lhsr = (lhsr & ~insmask) \
                   | ((*VL_GET_ELEM(rhsSuffix, lwp, lword) >> loffset) & (insmask & cleanmask)); \
        } else { \
            const int nbitsonright = VL_IDATASIZE - loffset; /* bits that filled by lword */ \
            const IData hinsmask = (VL_MASK_E(hoffset - 0 + 1)) << nbitsonright; \
            const IData linsmask = VL_MASK_E(VL_EDATASIZE - loffset); \
            lhsr = (lhsr & ~linsmask) \
                   | ((*VL_GET_ELEM(rhsSuffix, lwp, lword) >> loffset) & (linsmask & cleanmask)); \
            lhsr = (lhsr & ~hinsmask) \
                   | ((*VL_GET_ELEM(rhsSuffix, lwp, hword) << nbitsonright) \
                      & (hinsmask & cleanmask)); \
        } \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(_vl_insert_IW_GEN)
#undef _vl_insert_IW_GEN

// clang-format off
// INTERNAL: Stuff large LHS bit 0++ into OUTPUT at specified offset
// lwp may be "dirty"
#define _vl_insert_WW_GEN(outputSuffix, lhsSuffix) \
static inline void _vl_insert_WW_##outputSuffix##lhsSuffix(WDataOutP iowp, WDataInP const lwp, int hbit, int lbit, \
                                     int rbits = 0) VL_MT_SAFE { \
        const int hoffset = VL_BITBIT_E(hbit); \
        const int loffset = VL_BITBIT_E(lbit); \
        const int roffset = VL_BITBIT_E(rbits); \
        const int lword = VL_BITWORD_E(lbit); \
        const int hword = VL_BITWORD_E(hbit); \
        const int rword = VL_BITWORD_E(rbits); \
        const int words = VL_WORDS_I(hbit - lbit + 1); \
        /* Cleaning mask, only applied to top word of the assignment.  Is a no-op \
           if we don't assign to the top word of the destination. */ \
        const EData cleanmask = hword == rword ? VL_MASK_E(roffset) : VL_MASK_E(0); \
\
        if (hoffset == VL_SIZEBITS_E && loffset == 0) { \
            /* Fast and common case, word based insertion */ \
            for (int i = 0; i < (words - 1); ++i) *VL_GET_ELEM(outputSuffix, iowp, lword + i) = *VL_GET_ELEM(lhsSuffix, lwp, i); \
            *VL_GET_ELEM(outputSuffix, iowp, hword) = *VL_GET_ELEM(lhsSuffix, lwp, words - 1) & cleanmask; \
        } else if (loffset == 0) { \
            /* Non-32bit, but nicely aligned, so stuff all but the last word */ \
            for (int i = 0; i < (words - 1); ++i) *VL_GET_ELEM(outputSuffix, iowp, lword + i) = *VL_GET_ELEM(lhsSuffix, lwp, i); \
            /* Know it's not a full word as above fast case handled it */ \
            const EData hinsmask = (VL_MASK_E(hoffset - 0 + 1)); \
            *VL_GET_ELEM(outputSuffix, iowp, hword) = (*VL_GET_ELEM(outputSuffix, iowp, hword) & ~hinsmask) | (*VL_GET_ELEM(lhsSuffix, lwp, words - 1) & (hinsmask & cleanmask)); \
        } else { \
            const EData hinsmask = (VL_MASK_E(hoffset - 0 + 1)) << 0; \
            const EData linsmask = (VL_MASK_E((VL_EDATASIZE - 1) - loffset + 1)) << loffset; \
            const int nbitsonright \
                = VL_EDATASIZE - loffset; /* bits that end up in lword (know loffset!=0) */ \
            /* Middle words */ \
            for (int i = 0; i < words; ++i) { \
                { /* Lower word */ \
                    const int oword = lword + i; \
                    const EData d = *VL_GET_ELEM(lhsSuffix, lwp, i) << loffset; \
                    const EData od = (*VL_GET_ELEM(outputSuffix, iowp, oword) & ~linsmask) | (d & linsmask); \
                    if (oword == hword) { \
                        *VL_GET_ELEM(outputSuffix, iowp, oword) = (*VL_GET_ELEM(outputSuffix, iowp, oword) & ~hinsmask) | (od & (hinsmask & cleanmask)); \
                    } else { \
                        *VL_GET_ELEM(outputSuffix, iowp, oword) = od; \
                    } \
                } \
                { /* Upper word */ \
                    const int oword = lword + i + 1; \
                    if (oword <= hword) { \
                        const EData d = *VL_GET_ELEM(lhsSuffix, lwp, i) >> nbitsonright; \
                        const EData od = (d & ~linsmask) | (*VL_GET_ELEM(outputSuffix, iowp, oword) & linsmask); \
                        if (oword == hword) { \
                            *VL_GET_ELEM(outputSuffix, iowp, oword) \
                                = (*VL_GET_ELEM(outputSuffix, iowp, oword) & ~hinsmask) | (od & (hinsmask & cleanmask)); \
                        } else { \
                            *VL_GET_ELEM(outputSuffix, iowp, oword) = od; \
                        } \
                    } \
                } \
            } \
        } \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(_vl_insert_WW_GEN)

// clang-format off
#define _vl_insert_WQ_GEN(suffix) \
static inline void _vl_insert_WQ_##suffix(WDataOutP iowp, QData ld, int hbit, int lbit, \
                                          int rbits = 0) VL_MT_SAFE { \
        VlWide<VL_WQ_WORDS_E> lwp; \
        VL_SET_WQ_T(lwp, ld); \
        _vl_insert_WW_##suffix##T(iowp, lwp, hbit, lbit, rbits); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(_vl_insert_WQ_GEN)
#undef _vl_insert_WQ_GEN

// EMIT_RULE: VL_REPLICATE:  oclean=clean>width32, dirty<=width32; lclean=clean; rclean==clean;
// RHS MUST BE CLEAN CONSTANT.
#define VL_REPLICATE_IOI(lbits, ld, rep) (-(ld))  // Iff lbits==1
#define VL_REPLICATE_QOI(lbits, ld, rep) (-(static_cast<QData>(ld)))  // Iff lbits==1

static inline IData VL_REPLICATE_III_TTT(int lbits, IData ld, IData rep) VL_PURE {
    IData returndata = ld;
    for (unsigned i = 1; i < rep; ++i) {
        returndata = returndata << lbits;
        returndata |= ld;
    }
    return returndata;
}
static inline QData VL_REPLICATE_QII_TTT(int lbits, IData ld, IData rep) VL_PURE {
    QData returndata = ld;
    for (unsigned i = 1; i < rep; ++i) {
        returndata = returndata << lbits;
        returndata |= static_cast<QData>(ld);
    }
    return returndata;
}

// clang-format off
#define VL_REPLICATE_WII_GEN(outputSuffix) \
static inline WDataOutP VL_REPLICATE_WII_##outputSuffix##TT(int lbits, WDataOutP owp, \
                                                                IData ld, IData rep) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        *owp = ld; \
        /* Zeroing all words isn't strictly needed but allows compiler to know \
           it does not need to preserve data in word(s) not being written */ \
        for (unsigned i = 1; i < VL_WORDS_I(static_cast<unsigned>(lbits) * rep); ++i) { \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
            *owp = 0; \
        } \
        for (unsigned i = 1; i < rep; ++i) { \
            _vl_insert_WI_##outputSuffix(resultp, ld, i* lbits + lbits - 1, i * lbits); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_REPLICATE_WII_GEN)
#undef VL_REPLICATE_WII_GEN

// clang-format off
#define VL_REPLICATE_WQI_GEN(outputSuffix) \
static inline WDataOutP VL_REPLICATE_WQI_##outputSuffix##TT(int lbits, WDataOutP owp, \
                                                                QData ld, IData rep) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        VL_SET_WQ_##outputSuffix(owp, ld); \
        /* Zeroing all words isn't strictly needed but allows compiler to know \
           it does not need to preserve data in word(s) not being written */ \
        owp += VL_GET_TYPE_OFFSET(outputSuffix) + VL_GET_TYPE_JUMP(outputSuffix); \
        for (unsigned i = 2; i < VL_WORDS_I(static_cast<unsigned>(lbits) * rep); ++i) { \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
            *owp = 0; \
        } \
        for (unsigned i = 1; i < rep; ++i) { \
            _vl_insert_WQ_##outputSuffix(resultp, ld, i* lbits + lbits - 1, i * lbits); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_REPLICATE_WQI_GEN)
#undef VL_REPLICATE_WQI_GEN

// clang-format off
#define VL_REPLICATE_WWI_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_REPLICATE_WWI_##outputSuffix##lhsSuffix##T( \
        int lbits, WDataOutP owp, WDataInP const lwp, IData rep) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        VL_ASSIGN_W_##outputSuffix##lhsSuffix(lbits, owp, lwp); \
        /* Zeroing all words isn't strictly needed but allows compiler to know \
           it does not need to preserve data in word(s) not being written */ \
        int i = VL_WORDS_I(lbits); \
        owp += VL_GET_TYPE_OFFSET(outputSuffix) + i * VL_GET_TYPE_JUMP(outputSuffix); \
        for (; i < VL_WORDS_I(lbits * rep); ++i) { \
            *owp = 0; \
            owp += VL_GET_TYPE_JUMP(outputSuffix); \
        } \
        for (unsigned i = 1; i < rep; ++i) { \
            _vl_insert_WW_TT(resultp, lwp, i* lbits + lbits - 1, i * lbits); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_REPLICATE_WWI_GEN)
#undef VL_REPLICATE_WWI_GEN

// Left stream operator. Output will always be clean. LHS and RHS must be clean.
// Special "fast" versions for slice sizes that are a power of 2. These use
// shifts and masks to execute faster than the slower for-loop approach where a
// subset of bits is copied in during each iteration.
static inline IData VL_STREAML_FAST_III(int lbits, IData ld, IData rd_log2) VL_PURE {
    // Pre-shift bits in most-significant slice:
    //
    // If lbits is not a multiple of the slice size (i.e., lbits % rd != 0),
    // then we end up with a "gap" in our reversed result. For example, if we
    // have a 5-bit Verilog signal (lbits=5) in an 8-bit C data type:
    //
    //   ld = ---43210
    //
    // (where numbers are the Verilog signal bit numbers and '-' is an unused bit).
    // Executing the switch statement below with a slice size of two (rd=2,
    // rd_log2=1) produces:
    //
    //   ret = 1032-400
    //
    // Pre-shifting the bits in the most-significant slice allows us to avoid
    // this gap in the shuffled data:
    //
    //   ld_adjusted = --4-3210
    //   ret = 10324---
    IData ret = ld;
    if (rd_log2) {
        const uint32_t lbitsFloor = lbits & ~VL_MASK_I(rd_log2);  // max multiple of rd <= lbits
        const uint32_t lbitsRem = lbits - lbitsFloor;  // number of bits in most-sig slice (MSS)
        const IData msbMask = lbitsFloor == 32 ? 0UL : VL_MASK_I(lbitsRem) << lbitsFloor;
        ret = (ret & ~msbMask) | ((ret & msbMask) << ((VL_UL(1) << rd_log2) - lbitsRem));
    }
    switch (rd_log2) {
    case 0: ret = ((ret >> 1) & VL_UL(0x55555555)) | ((ret & VL_UL(0x55555555)) << 1);  // FALLTHRU
    case 1: ret = ((ret >> 2) & VL_UL(0x33333333)) | ((ret & VL_UL(0x33333333)) << 2);  // FALLTHRU
    case 2: ret = ((ret >> 4) & VL_UL(0x0f0f0f0f)) | ((ret & VL_UL(0x0f0f0f0f)) << 4);  // FALLTHRU
    case 3: ret = ((ret >> 8) & VL_UL(0x00ff00ff)) | ((ret & VL_UL(0x00ff00ff)) << 8);  // FALLTHRU
    case 4: ret = ((ret >> 16) | (ret << 16));  // FALLTHRU
    default:;
    }
    return ret >> (VL_IDATASIZE - lbits);
}

static inline QData VL_STREAML_FAST_QQI(int lbits, QData ld, IData rd_log2) VL_PURE {
    // Pre-shift bits in most-significant slice (see comment in VL_STREAML_FAST_III)
    QData ret = ld;
    if (rd_log2) {
        const uint32_t lbitsFloor = lbits & ~VL_MASK_I(rd_log2);
        const uint32_t lbitsRem = lbits - lbitsFloor;
        const QData msbMask = lbitsFloor == 64 ? 0ULL : VL_MASK_Q(lbitsRem) << lbitsFloor;
        ret = (ret & ~msbMask) | ((ret & msbMask) << ((1ULL << rd_log2) - lbitsRem));
    }
    switch (rd_log2) {
    case 0:
        ret = (((ret >> 1) & 0x5555555555555555ULL)
               | ((ret & 0x5555555555555555ULL) << 1));  // FALLTHRU
    case 1:
        ret = (((ret >> 2) & 0x3333333333333333ULL)
               | ((ret & 0x3333333333333333ULL) << 2));  // FALLTHRU
    case 2:
        ret = (((ret >> 4) & 0x0f0f0f0f0f0f0f0fULL)
               | ((ret & 0x0f0f0f0f0f0f0f0fULL) << 4));  // FALLTHRU
    case 3:
        ret = (((ret >> 8) & 0x00ff00ff00ff00ffULL)
               | ((ret & 0x00ff00ff00ff00ffULL) << 8));  // FALLTHRU
    case 4:
        ret = (((ret >> 16) & 0x0000ffff0000ffffULL)
               | ((ret & 0x0000ffff0000ffffULL) << 16));  // FALLTHRU
    case 5: ret = ((ret >> 32) | (ret << 32));  // FALLTHRU
    default:;
    }
    return ret >> (VL_QUADSIZE - lbits);
}

template <typename T>
static inline void VL_STREAML_FAST_RQI(int lbits, VlQueue<T>& q, QData ld, IData rd_log2) VL_PURE {
    const QData ret = VL_STREAML_FAST_QQI(lbits, ld, rd_log2);
    q.clear();
    const int numQData = 8 / sizeof(T);
    const bool needsMask = sizeof(T) < 8;
    for (int ii = numQData - 1; ii >= 0; ii--) {
        if VL_CONSTEXPR_CXX17 (needsMask) {
            VL_CONSTEXPR_CXX17 uint64_t mask = VL_MASK_Q(sizeof(T) * 8);
            q.push_back(static_cast<T>(ret >> (ii * sizeof(T) * 8)) & mask);
        } else {
            q.push_back(static_cast<T>(ret));
        }
    }
}

template <std::size_t N_Words>
static inline void VL_STREAML_FAST_RQI(int lbits, VlQueue<VlWide<N_Words>>& q, QData ld,
                                       IData rd_log2) VL_PURE {
    const QData ret = VL_STREAML_FAST_QQI(lbits, ld, rd_log2);
    q.clear();
    VlWide<N_Words> value;
    value[N_Words - 1] = static_cast<EData>(ret >> 32);
    value[N_Words - 2] = static_cast<EData>(ret);
    for (int i = N_Words - 3; i >= 0; i--) value[i] = 0;
    q.push_back(value);
}

template <typename T>
static inline void VL_STREAMR_RII(int lbits, VlQueue<T>& q, IData ld, IData rd_log2) VL_PURE {
    q.clear();
    VL_CONSTEXPR_CXX17 int valueSize = sizeof(T);
    if VL_CONSTEXPR_CXX17 (valueSize < 4) {
        VL_CONSTEXPR_CXX17 int mask = VL_MASK_I(valueSize * 8);
        // Push all bytes of the 32-bit integer, MSB first (Big-Endian)
        VL_CONSTEXPR_CXX17 int qElementsPerWord = 4 / valueSize;
        for (int i = 0; i < qElementsPerWord; i++) {
            q.push_back(
                static_cast<T>(((ld >> (qElementsPerWord - i - 1) * 8 * valueSize)) & mask));
        }
    } else {
        q.push_back(static_cast<T>(ld));
    }
}

template <std::size_t N_Words>
static inline void VL_STREAMR_RII(int lbits, VlQueue<VlWide<N_Words>>& q, IData ld,
                                  IData rd_log2) VL_PURE {
    q.clear();
    VlWide<N_Words> value;
    VL_SET_WI(value, ld);
    q.push_back(value);
}

template <typename T>
static inline void VL_STREAMR_RQI(int lbits, VlQueue<T>& q, QData ld, IData rd_log2) VL_PURE {
    q.clear();  // Empty the queue first
    // If this is a queue of bytes (unsigned char)
    if VL_CONSTEXPR_CXX17 (sizeof(T) == 1) {
        // Push all 8 bytes of the 64-bit integer, MSB first (Big-Endian)
        q.push_back(static_cast<T>((ld >> 56) & 0xFF));
        q.push_back(static_cast<T>((ld >> 48) & 0xFF));
        q.push_back(static_cast<T>((ld >> 40) & 0xFF));
        q.push_back(static_cast<T>((ld >> 32) & 0xFF));
        q.push_back(static_cast<T>((ld >> 24) & 0xFF));
        q.push_back(static_cast<T>((ld >> 16) & 0xFF));
        q.push_back(static_cast<T>((ld >> 8) & 0xFF));
        q.push_back(static_cast<T>(ld & 0xFF));
    } else {
        const int numQData = 8 / sizeof(T);
        for (int ii = numQData - 1; ii >= 0; ii--) {
            q.push_back(static_cast<T>(ld >> (ii * sizeof(T) * 8)));
        }
    }
}

template <typename T>
static inline IData VL_STREAMR_IRI(int lbits, VlQueue<T>& q, IData rd_log2) VL_PURE {
    IData value = 0;  // Starts at 0. Out-of-range bits will remain 0.
    const size_t len = q.size();

    if VL_CONSTEXPR_CXX17 (sizeof(T) == 1) {  // If it is a queue of bytes
        if (len > 0) value |= static_cast<IData>(q.at(0)) << 24;
        if (len > 1) value |= static_cast<IData>(q.at(1)) << 16;
        if (len > 2) value |= static_cast<IData>(q.at(2)) << 8;
        if (len > 3) value |= static_cast<IData>(q.at(3));
    } else if VL_CONSTEXPR_CXX17 (sizeof(T) == 2) {
        if (len > 0) value |= static_cast<IData>(q.at(0)) << 16;
        if (len > 1) value |= static_cast<IData>(q.at(1));
    } else if VL_CONSTEXPR_CXX17 (sizeof(T) == 8) {
        if (len > 0) value = static_cast<IData>(q.at(0));
    } else {  // If it is a queue of larger types (e.g. ints)
        VL_CONSTEXPR_CXX17 int shiftAmt = sizeof(T) > 4 ? 32 : 0;
        if (len > 0) value = static_cast<IData>(q.at(0) >> shiftAmt);
    }

    return value;
}

template <typename T>
static inline IData VL_STREAMR_QRI(int lbits, VlQueue<T>& q, IData rd_log2) VL_PURE {
    QData value = 0;
    const size_t len = q.size();

    if VL_CONSTEXPR_CXX17 (sizeof(T) == 1) {
        // Must cast to QData BEFORE shifting to prevent 32-bit overflow!
        if (len > 0) value |= static_cast<QData>(q.at(0)) << 56;
        if (len > 1) value |= static_cast<QData>(q.at(1)) << 48;
        if (len > 2) value |= static_cast<QData>(q.at(2)) << 40;
        if (len > 3) value |= static_cast<QData>(q.at(3)) << 32;
        if (len > 4) value |= static_cast<QData>(q.at(4)) << 24;
        if (len > 5) value |= static_cast<QData>(q.at(5)) << 16;
        if (len > 6) value |= static_cast<QData>(q.at(6)) << 8;
        if (len > 7) value |= static_cast<QData>(q.at(7));
    } else {
        // If it is a queue of larger types (e.g. ints/longs)
        if (len > 0) value = static_cast<QData>(q.at(0));
    }

    return value;
}

template <std::size_t N_Words>
static inline void VL_STREAMR_RQI(int lbits, VlQueue<VlWide<N_Words>>& q, QData ld,
                                  IData rd_log2) VL_PURE {
    q.clear();  // Empty the queue first
    VlWide<N_Words> value;
    VL_SET_WQ_T(value, ld);
    q.push_back(value);
}

template <typename T>
static inline void VL_STREAMR_RWI(int lbits, VlQueue<T>& q, WDataInP const lwp,
                                  IData rd_log2) VL_PURE {
    q.clear();  // Empty the queue first
    const int numWords = VL_BITWORD_E(lbits);
    QData qdataValue = 0;
    for (int word = numWords - 1; word >= 0; word--) {
        constexpr int valueSize = sizeof(T);
        if VL_CONSTEXPR_CXX17 (valueSize < 4) {
            constexpr int mask = VL_MASK_I(valueSize * 8);
            // Push all bytes of the 32-bit integer, MSB first (Big-Endian)
            constexpr int qElementsPerWord = 4 / valueSize;
            for (int i = 0; i < qElementsPerWord; i++) {
                q.push_back(static_cast<T>(
                    ((lwp[word] >> (qElementsPerWord - i - 1) * 8 * valueSize)) & mask));
            }
        } else if VL_CONSTEXPR_CXX17 (sizeof(T) == 8) {
            const int shiftAmt = (word & 0x1) << 5;
            qdataValue |= static_cast<QData>(lwp[word]) << shiftAmt;
            if ((word & 0x1) == 0) {
                q.push_back(qdataValue);
                qdataValue = 0;
            }
        } else {
            q.push_back(static_cast<T>(lwp[word]));
        }
    }
}

template <std::size_t N_Words>
static inline void VL_STREAMR_RWI(int lbits, VlQueue<VlWide<N_Words>>& q, WDataInP const lwp,
                                  IData rd_log2) VL_PURE {
    q.clear();  // Empty the queue first
    const int numWords = VL_BITWORD_E(lbits);
    VlWide<N_Words> value;
    for (int ii = 0; ii < N_Words; ii++) { value.at(ii) = 0; }
    for (int word = numWords - 1; word >= 0; word--) {
        value.at(word) = lwp[word];
        if ((word % N_Words) == 0) { q.push_back(value); }
    }
}

template <typename T>
static inline VlQueue<T> VL_STREAMR_RRI(int lbits, const VlQueue<T> q, IData rd) VL_MT_SAFE {
    return q;
}

static inline VlQueue<std::string> VL_STREAMR_NRI(int lbits, const VlQueue<std::string> q,
                                                  IData rd) VL_MT_SAFE {
    return q;
}

template <typename T_Value, typename T_Other>
static inline void VL_STREAMR_RRI(int lbits, VlQueue<T_Value>& to_q,
                                  const VlQueue<T_Other>& from_q, IData rd) VL_MT_SAFE {
    to_q.clear();
    VL_CONSTEXPR_CXX17 size_t otherSize = sizeof(T_Other);
    VL_CONSTEXPR_CXX17 size_t sizeOfThis = sizeof(T_Value);
    T_Value temp = 0;
    if (otherSize > sizeOfThis) {
        for (auto val : from_q) {
            for (int ii = otherSize / sizeOfThis - 1; ii >= 0; ii--) {
                temp = (static_cast<T_Value>(val >> (ii * 8 * sizeOfThis)));
                to_q.push_back(temp);
            }
        }
    } else {
        // How many of the other element fits in this element.
        size_t otherInElement = sizeOfThis / otherSize - 1;
        for (auto val : from_q) {
            // Shift the element into the correct position and merge
            temp |= (static_cast<T_Value>(val) << (otherInElement * 8 * otherSize));
            otherInElement--;
            if (otherInElement == -1) {
                to_q.push_back(temp);
                temp = 0;
                otherInElement = sizeOfThis - 1;
            }
        }
        // Push any remaining leftover elements (upper bits will remain zero-padded)
        if (otherInElement < sizeOfThis - 1) { to_q.push_back(temp); }
    }
}

template <typename T_Other, std::size_t N_Words>
static inline void VL_STREAMR_RRI(int lbits, VlQueue<VlWide<N_Words>>& to_q,
                                  const VlQueue<T_Other>& from_q, IData rd) VL_MT_SAFE {
    to_q.clear();

    VL_CONSTEXPR_CXX17 size_t otherSize = sizeof(T_Other);
    VL_CONSTEXPR_CXX17 size_t sizeOfThis = 4 * N_Words;
    VL_CONSTEXPR_CXX17 int numOtherInWord = 4 / otherSize;
    VlWide<N_Words> temp;
    for (int ii = 0; ii < N_Words; ii++) { temp.at(ii) = 0; }
    if VL_CONSTEXPR_CXX17 (numOtherInWord > 0) {
        size_t elementCount = sizeOfThis - 1;
        for (auto val : from_q) {
            temp.at((elementCount / numOtherInWord) % N_Words)
                |= (static_cast<EData>(val) << (elementCount * 8 * otherSize));
            elementCount--;
            // If we've collected enough elements for the target type, push and reset
            if (elementCount == -1) {
                to_q.push_back(temp);
                for (int ii = 0; ii < N_Words; ii++) { temp.at(ii) = 0; }
                elementCount = sizeOfThis - 1;
            }
        }
        // Push any remaining leftover elements (upper bits will remain zero-padded)
        if (elementCount < sizeOfThis - 1) { to_q.push_back(temp); }
    } else {  //QData
        size_t wordCount = N_Words - 1;
        for (auto val : from_q) {
            temp.at(wordCount % N_Words) = (static_cast<EData>(static_cast<QData>(val) >> 32));
            wordCount--;
            if (wordCount == -1) {
                to_q.push_back(temp);
                for (int ii = 0; ii < N_Words; ii++) { temp.at(ii) = 0; }
                wordCount = N_Words - 1;
            }
            temp.at(wordCount % N_Words) = (static_cast<EData>(val));
            wordCount--;
            if (wordCount == -1) {
                to_q.push_back(temp);
                for (int ii = 0; ii < N_Words; ii++) { temp.at(ii) = 0; }
                wordCount = N_Words - 1;
            }
        }
        // Push any remaining leftover elements (upper bits will remain zero-padded)
        if (wordCount < N_Words - 1) { to_q.push_back(temp); }
    }
}

template <typename T_Value, std::size_t N_Words>
static inline void VL_STREAMR_RRI(int lbits, VlQueue<T_Value>& to_q,
                                  const VlQueue<VlWide<N_Words>>& from_q, IData rd) VL_MT_SAFE {
    to_q.clear();

    VL_CONSTEXPR_CXX17 size_t otherSize = 4 * N_Words;
    VL_CONSTEXPR_CXX17 size_t sizeOfThis = sizeof(T_Value);
    T_Value temp = 0;
    for (auto val : from_q) {
        if VL_CONSTEXPR_CXX17 (sizeof(T_Value) == 8) {
            // iterate backwards because queues are msb first
            for (int wordIndex = N_Words - 1; wordIndex >= 0; wordIndex -= 2) {
                temp |= (static_cast<T_Value>(val.at(wordIndex)) << 32);
                if (wordIndex - 1 >= 0) { temp |= (static_cast<T_Value>(val.at(wordIndex - 1))); }
                to_q.push_back(temp);
                temp = 0;
            }
        } else {
            //iterate backwards because queues are msb first
            for (int wordIndex = N_Words - 1; wordIndex >= 0; wordIndex--) {
                for (int elemInWord = sizeof(EData) / sizeOfThis - 1; elemInWord >= 0;
                     elemInWord--) {
                    temp
                        = (static_cast<T_Value>(val.at(wordIndex) >> elemInWord * 8 * sizeOfThis));
                    to_q.push_back(temp);
                }
            }
        }
    }
}

// Regular "slow" streaming operators
static inline IData VL_STREAML_III(int lbits, IData ld, IData rd) VL_PURE {
    IData ret = 0;
    // Slice size should never exceed the lhs width
    const IData mask = VL_MASK_I(rd);
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        ret |= ((ld >> istart) & mask) << ostart;
    }
    return ret;
}

template <typename T>
static inline VlQueue<T> VL_STREAML_RRI(int lbitsIn, const VlQueue<T> q, IData rd) VL_MT_SAFE {
    // TODO this function needs to have a temp variable made in verilator and passed in.
    // dynamicly make our "temp variable"
    // lbitsIn is always 0
    VlQueue<T> out_queue;
    const int lbits = q.size() * 8 * sizeof(T);
    out_queue.renew(q.size());
    VL_CONSTEXPR_CXX17 unsigned int moduloMask = 8 * sizeof(T) - 1;
    const int ssize = (rd < static_cast<IData>(lbits)) ? rd : (static_cast<IData>(lbits));
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        for (int sbit = 0; sbit < ssize && sbit < lbits - istart; ++sbit) {

            const int qIndex = (ostart + sbit) / (8 * sizeof(T));
            const int shiftLeft = (istart + sbit) & moduloMask;
            const int shiftRight = ((ostart + sbit) & moduloMask);
            const T bit = ((q.at(qIndex)) >> shiftRight & 1) << shiftLeft;
            const int writeIndx = (istart + sbit) / (8 * sizeof(T));
            out_queue.atWrite(writeIndx) |= bit;
        }
    }

    return out_queue;
}

template <std::size_t N_Words>
static inline VlQueue<VlWide<N_Words>>
VL_STREAML_RRI(int lbitsIn, const VlQueue<VlWide<N_Words>> q, IData rd) VL_MT_SAFE {
    // TODO this function needs to have a temp variable.
    // dynamicly make our "temp variable"
    // lbitsIn is always zero
    const int lbits = q.size() * 8 * sizeof(IData) * N_Words;
    VL_CONSTEXPR_CXX17 int sizeOfElement = 8 * sizeof(IData) * N_Words;
    VlQueue<VlWide<N_Words>> out_queue;
    out_queue.renew(q.size());
    VL_CONSTEXPR_CXX17 unsigned int moduloMask = sizeOfElement - 1;
    const int ssize = (rd < static_cast<IData>(lbits)) ? rd : (static_cast<IData>(lbits));
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        for (int sbit = 0; sbit < ssize && sbit < lbits - istart; ++sbit) {

            const int qIndex = (ostart + sbit) / (sizeOfElement);
            const int shiftLeftTotal = (istart + sbit) & moduloMask;
            const int shiftRightTotal = ((ostart + sbit) & moduloMask);
            const int shiftRight = VL_MASK_I(shiftRightTotal);
            const int wordIn = VL_BITWORD_E(shiftRightTotal);
            const int shiftLeft = VL_MASK_I(shiftLeftTotal);
            const int wordOut = VL_BITWORD_E(shiftLeftTotal);
            const EData bit = ((q.at(qIndex).at(wordIn)) >> shiftRight & 1) << shiftLeft;
            const int writeIndx = (istart + sbit) / (sizeOfElement);
            out_queue.atWrite(writeIndx).at(wordOut) |= bit;
        }
    }

    return out_queue;
}

template <typename T>
static inline void VL_STREAML_RII(int lbits, int queueBits, VlQueue<T>& q, IData ld,
                                  IData rd) VL_MT_SAFE {

    IData ret = 0;
    if (lbits < queueBits) { lbits = queueBits; }
    // Slice size should never exceed the lhs width
    const IData mask = VL_MASK_I(rd);
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        ret |= ((ld >> istart) & mask) << ostart;
    }
    q.clear();
    VL_CONSTEXPR_CXX17 int numBitsPerQElem = sizeof(T) * 8;
    const bool needsMask = sizeof(T) < 4;
    VL_CONSTEXPR_CXX17 int elementMask = VL_MASK_I(numBitsPerQElem * needsMask);
    VL_CONSTEXPR_CXX17 int qElementPerWord = numBitsPerQElem < 32 ? 32 / numBitsPerQElem : 1;
    for (int i = 0; i < qElementPerWord; i++) {
        if VL_CONSTEXPR_CXX17 (needsMask) {
            q.push_back(static_cast<T>(((ret >> (qElementPerWord - i - 1) * numBitsPerQElem))
                                       & elementMask));
        } else {
            q.push_back(static_cast<T>((ret)));
        }
    }
}

template <std::size_t N_Words>
static inline void VL_STREAML_RII(int lbits, int queueBits, VlQueue<VlWide<N_Words>>& q, IData ld,
                                  IData rd) VL_MT_SAFE {
    if (lbits < queueBits) { lbits = queueBits; }
    IData ret = 0;
    // Slice size should never exceed the lhs width
    const IData mask = VL_MASK_I(rd);
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        ret |= ((ld >> istart) & mask) << ostart;
    }
    q.clear();
    VlWide<N_Words> value;
    value[0] = ret;
    q.push_back(value);
}

static inline QData VL_STREAML_QQI(int lbits, QData ld, IData rd) VL_PURE {
    QData ret = 0;
    // Slice size should never exceed the lhs width
    const QData mask = VL_MASK_Q(rd);
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        ret |= ((ld >> istart) & mask) << ostart;
    }
    return ret;
}

static inline WDataOutP VL_STREAML_WWI(int lbits, WDataOutP owp, WDataInP const lwp,
                                       IData rd) VL_MT_SAFE {
    VL_ZERO_W_T(lbits, owp);
    // Slice size should never exceed the lhs width
    const int ssize = (rd < static_cast<IData>(lbits)) ? rd : (static_cast<IData>(lbits));
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        for (int sbit = 0; sbit < ssize && sbit < lbits - istart; ++sbit) {
            // Extract a single bit from lwp and shift it to the correct
            // location for owp.
            const EData bit = (VL_BITRSHIFT_W(lwp, (istart + sbit)) & 1)
                              << VL_BITBIT_E(ostart + sbit);
            owp[VL_BITWORD_E(ostart + sbit)] |= bit;
        }
    }
    return owp;
}

template <typename T>
static inline void VL_STREAML_RWI(int lbits, int queueBits, VlQueue<T>& q, WDataInP const lwp,
                                  IData rd) VL_MT_SAFE {
    const bool needsMask = sizeof(T) < 4;
    VL_CONSTEXPR_CXX17 int numBitsInT = 8 * sizeof(T);
    VL_CONSTEXPR_CXX17 int mask = VL_MASK_I(numBitsInT * needsMask);
    q.renew(lbits / numBitsInT);
    const int ssize = (rd < static_cast<IData>(lbits)) ? rd : (static_cast<IData>(lbits));
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        for (int sbit = 0; sbit < ssize && sbit < lbits - istart; ++sbit) {
            const EData bit = (VL_BITRSHIFT_W(lwp, (istart + sbit)) & 1)
                              << VL_BITBIT_E(ostart + sbit);
            int qIndex = istart / numBitsInT;
            if VL_CONSTEXPR_CXX17 (needsMask) {
                int elementInWord = VL_BITBIT_I(ostart + sbit) / numBitsInT;
                elementInWord *= numBitsInT;
                q.atWrite(qIndex) |= (bit >> elementInWord) & mask;
            } else if VL_CONSTEXPR_CXX17 (sizeof(T) > 4) {
                int wordInElement = VL_BITBIT_Q(ostart) > 32;
                wordInElement *= 32;
                q.atWrite(qIndex) |= static_cast<T>(bit) << wordInElement;
            } else {
                q.atWrite(qIndex) |= (bit);
            }
        }
    }
}

template <std::size_t N_Words>
static inline void VL_STREAML_RWI(int lbits, int queueBits, VlQueue<VlWide<N_Words>>& q,
                                  WDataInP const lwp, IData rd) VL_MT_SAFE {
    VL_CONSTEXPR_CXX17 int numBitsInT = 4 * N_Words * 8;
    if (lbits < queueBits) {  // this handles the case where the queue is larger than the rhs
        lbits = queueBits;
    }
    const int leftOver = (lbits % numBitsInT) > 0;
    q.renew(lbits / numBitsInT + leftOver);
    const int ssize = (rd < static_cast<IData>(lbits)) ? rd : (static_cast<IData>(lbits));
    for (int istart = 0; istart < lbits; istart += rd) {
        int ostart = lbits - rd - istart;
        ostart = ostart > 0 ? ostart : 0;
        for (int sbit = 0; sbit < ssize && sbit < lbits - istart; ++sbit) {
            const EData bit = (VL_BITRSHIFT_W(lwp, (istart + sbit)) & 1)
                              << VL_BITBIT_E(ostart + sbit);
            int qIndex = istart / numBitsInT;
            int wordInWide = VL_BITWORD_E(ostart % numBitsInT);
            q.atWrite(qIndex).at(wordInWide) |= (bit);
        }
    }
}

static inline IData VL_PACK_I_RI(int /*obits*/, int lbits, const VlQueue<CData>& q) {
    IData ret = 0;
    for (size_t i = 0; i < q.size(); ++i)
        ret |= static_cast<IData>(q.at(q.size() - 1 - i)) << (i * lbits);
    return ret;
}

static inline IData VL_PACK_I_RI(int /*obits*/, int lbits, const VlQueue<SData>& q) {
    IData ret = 0;
    for (size_t i = 0; i < q.size(); ++i)
        ret |= static_cast<IData>(q.at(q.size() - 1 - i)) << (i * lbits);
    return ret;
}

static inline IData VL_PACK_I_RI(int /*obits*/, int lbits, const VlQueue<IData>& q) {
    IData ret = 0;
    for (size_t i = 0; i < q.size(); ++i) ret |= q.at(q.size() - 1 - i) << (i * lbits);
    return ret;
}

template <typename T>
struct VlUnpackedElements final {
    static constexpr size_t count = 1;
};

template <typename T, size_t N>
struct VlUnpackedElements<VlUnpacked<T, N>> final {
    static constexpr size_t count = N * VlUnpackedElements<T>::count;
};

template <std::size_t N_Depth>
static inline IData VL_PACK_I_UI(int /*obits*/, int lbits, const VlUnpacked<CData, N_Depth>& q) {
    IData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i)
        ret |= static_cast<IData>(q[N_Depth - 1 - i]) << (i * lbits);
    return ret;
}

template <std::size_t N_Depth>
static inline IData VL_PACK_I_UI(int /*obits*/, int lbits, const VlUnpacked<SData, N_Depth>& q) {
    IData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i)
        ret |= static_cast<IData>(q[N_Depth - 1 - i]) << (i * lbits);
    return ret;
}

template <std::size_t N_Depth>
static inline IData VL_PACK_I_UI(int /*obits*/, int lbits, const VlUnpacked<IData, N_Depth>& q) {
    IData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i) ret |= q[N_Depth - 1 - i] << (i * lbits);
    return ret;
}

template <typename T_Sub, std::size_t N_Sub, std::size_t N_Depth>
static inline IData VL_PACK_I_UI(const int obits, const int lbits,
                                 const VlUnpacked<VlUnpacked<T_Sub, N_Sub>, N_Depth>& q) {
    IData ret = 0;
    const int sub_bits = VlUnpackedElements<VlUnpacked<T_Sub, N_Sub>>::count * lbits;
    for (size_t i = 0; i < N_Depth; ++i) {
        const IData sub_val = VL_PACK_I_UI(sub_bits, lbits, q[N_Depth - 1 - i]);
        ret |= sub_val << (i * sub_bits);
    }
    return ret;
}

static inline QData VL_PACK_Q_RI(int /*obits*/, int lbits, const VlQueue<CData>& q) {
    QData ret = 0;
    for (size_t i = 0; i < q.size(); ++i)
        ret |= static_cast<QData>(q.at(q.size() - 1 - i)) << (i * lbits);
    return ret;
}

static inline QData VL_PACK_Q_RI(int /*obits*/, int lbits, const VlQueue<SData>& q) {
    QData ret = 0;
    for (size_t i = 0; i < q.size(); ++i)
        ret |= static_cast<QData>(q.at(q.size() - 1 - i)) << (i * lbits);
    return ret;
}

static inline QData VL_PACK_Q_RI(int /*obits*/, int lbits, const VlQueue<IData>& q) {
    QData ret = 0;
    for (size_t i = 0; i < q.size(); ++i)
        ret |= static_cast<QData>(q.at(q.size() - 1 - i)) << (i * lbits);
    return ret;
}

template <std::size_t N_Depth>
static inline QData VL_PACK_Q_UI(int /*obits*/, int lbits, const VlUnpacked<CData, N_Depth>& q) {
    QData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i)
        ret |= static_cast<QData>(q[N_Depth - 1 - i]) << (i * lbits);
    return ret;
}

template <std::size_t N_Depth>
static inline QData VL_PACK_Q_UI(int /*obits*/, int lbits, const VlUnpacked<SData, N_Depth>& q) {
    QData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i)
        ret |= static_cast<QData>(q[N_Depth - 1 - i]) << (i * lbits);
    return ret;
}

template <std::size_t N_Depth>
static inline QData VL_PACK_Q_UI(int /*obits*/, int lbits, const VlUnpacked<IData, N_Depth>& q) {
    QData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i)
        ret |= static_cast<QData>(q[N_Depth - 1 - i]) << (i * lbits);
    return ret;
}

static inline QData VL_PACK_Q_RQ(int /*obits*/, int lbits, const VlQueue<QData>& q) {
    QData ret = 0;
    for (size_t i = 0; i < q.size(); ++i) ret |= q.at(q.size() - 1 - i) << (i * lbits);
    return ret;
}

static inline IData VL_PACK_I_RQ(int /*obits*/, int lbits, const VlQueue<QData>& q) {
    IData ret = 0;
    for (size_t i = 0; i < q.size(); ++i) ret |= q.at(q.size() - 1 - i) << (i * lbits);
    return ret;
}

template <std::size_t N_Words>
static inline IData VL_PACK_I_RW(int /*obits*/, int lbits, const VlQueue<VlWide<N_Words>>& q) {
    IData ret = 0;
    for (size_t i = 0; i < q.size(); ++i) ret |= q.at(q.size() - 1 - i)[0] << (i * lbits);
    return ret;
}

template <std::size_t N_Depth>
static inline QData VL_PACK_Q_UQ(int /*obits*/, int lbits, const VlUnpacked<QData, N_Depth>& q) {
    QData ret = 0;
    for (size_t i = 0; i < N_Depth; ++i) ret |= q[N_Depth - 1 - i] << (i * lbits);
    return ret;
}

static inline WDataOutP VL_PACK_W_RI(int obits, int lbits, WDataOutP owp,
                                     const VlQueue<CData>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    if (VL_UNLIKELY(obits < q.size() * lbits)) return owp;  // Though is illegal for q to be larger
    const int offset = obits - q.size() * lbits;
    for (size_t i = 0; i < q.size(); ++i)
        _vl_insert_WI_T(owp, q.at(q.size() - i - 1), i * lbits + lbits - 1 + offset,
                        i * lbits + offset);
    return owp;
}

static inline WDataOutP VL_PACK_W_RI(int obits, int lbits, WDataOutP owp,
                                     const VlQueue<SData>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    if (VL_UNLIKELY(obits < q.size() * lbits)) return owp;  // Though is illegal for q to be larger
    const int offset = obits - q.size() * lbits;
    for (size_t i = 0; i < q.size(); ++i)
        _vl_insert_WI_T(owp, q.at(q.size() - i - 1), i * lbits + lbits - 1 + offset,
                        i * lbits + offset);
    return owp;
}

static inline WDataOutP VL_PACK_W_RI(int obits, int lbits, WDataOutP owp,
                                     const VlQueue<IData>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    if (VL_UNLIKELY(obits < q.size() * lbits)) return owp;  // Though is illegal for q to be larger
    const int offset = obits - q.size() * lbits;
    for (size_t i = 0; i < q.size(); ++i)
        _vl_insert_WI_T(owp, q.at(q.size() - 1 - i), i * lbits + lbits - 1 + offset,
                        i * lbits + offset);
    return owp;
}

template <std::size_t N_Depth>
static inline WDataOutP VL_PACK_W_UI(int obits, int lbits, WDataOutP owp,
                                     const VlUnpacked<CData, N_Depth>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    for (size_t i = 0; i < N_Depth; ++i)
        _vl_insert_WI_T(owp, q[N_Depth - 1 - i], i * lbits + lbits - 1, i * lbits);
    return owp;
}

template <std::size_t N_Depth>
static inline WDataOutP VL_PACK_W_UI(int obits, int lbits, WDataOutP owp,
                                     const VlUnpacked<SData, N_Depth>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    for (size_t i = 0; i < N_Depth; ++i)
        _vl_insert_WI_T(owp, q[N_Depth - 1 - i], i * lbits + lbits - 1, i * lbits);
    return owp;
}

template <std::size_t N_Depth>
static inline WDataOutP VL_PACK_W_UI(int obits, int lbits, WDataOutP owp,
                                     const VlUnpacked<IData, N_Depth>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    for (size_t i = 0; i < N_Depth; ++i)
        _vl_insert_WI_T(owp, q[N_Depth - 1 - i], i * lbits + lbits - 1, i * lbits);
    return owp;
}

static inline WDataOutP VL_PACK_W_RQ(int obits, int lbits, WDataOutP owp,
                                     const VlQueue<QData>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    if (VL_UNLIKELY(obits < q.size() * lbits)) return owp;  // Though is illegal for q to be larger
    const int offset = obits - q.size() * lbits;
    for (size_t i = 0; i < q.size(); ++i)
        _vl_insert_WQ_T(owp, q.at(q.size() - 1 - i), i * lbits + lbits - 1 + offset,
                        i * lbits + offset);
    return owp;
}

template <std::size_t N_Depth>
static inline WDataOutP VL_PACK_W_UQ(int obits, int lbits, WDataOutP owp,
                                     const VlUnpacked<QData, N_Depth>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    for (size_t i = 0; i < N_Depth; ++i)
        _vl_insert_WQ_T(owp, q[N_Depth - 1 - i], i * lbits + lbits - 1, i * lbits);
    return owp;
}

template <std::size_t N_Words>
static inline WDataOutP VL_PACK_W_RW(int obits, int lbits, WDataOutP owp,
                                     const VlQueue<VlWide<N_Words>>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    if (VL_UNLIKELY(obits < q.size() * lbits)) return owp;  // Though is illegal for q to be larger
    const int offset = obits - q.size() * lbits;
    for (size_t i = 0; i < q.size(); ++i)
        _vl_insert_WW_TT(owp, q.at(q.size() - 1 - i), i * lbits + lbits - 1 + offset,
                         i * lbits + offset);
    return owp;
}

template <std::size_t N_Depth, std::size_t N_Words>
static inline WDataOutP VL_PACK_W_UW(int obits, int lbits, WDataOutP owp,
                                     const VlUnpacked<VlWide<N_Words>, N_Depth>& q) {
    VL_MEMSET_ZERO_W(owp + 1, VL_WORDS_I(obits) - 1);
    if (VL_UNLIKELY(obits < q.size() * lbits)) return owp;  // Though is illegal for q to be larger
    const int offset = obits - q.size() * lbits;
    for (size_t i = 0; i < N_Depth; ++i)
        _vl_insert_WW_TT(owp, q[N_Depth - 1 - i], i * lbits + lbits - 1 + offset,
                         i * lbits + offset);
    return owp;
}

// Because concats are common and wide, it's valuable to always have a clean output.
// Thus we specify inputs must be clean, so we don't need to clean the output.
// Note the bit shifts are always constants, so the adds in these constify out.
// Casts required, as args may be 8 bit entities, and need to shift to appropriate output size
#define VL_CONCAT_III_TTT(obits, lbits, rbits, ld, rd) \
    (static_cast<IData>(ld) << (rbits) | static_cast<IData>(rd))
#define VL_CONCAT_QII_TTT(obits, lbits, rbits, ld, rd) \
    (static_cast<QData>(ld) << (rbits) | static_cast<QData>(rd))
#define VL_CONCAT_QIQ_TTT(obits, lbits, rbits, ld, rd) \
    (static_cast<QData>(ld) << (rbits) | static_cast<QData>(rd))
#define VL_CONCAT_QQI_TTT(obits, lbits, rbits, ld, rd) \
    (static_cast<QData>(ld) << (rbits) | static_cast<QData>(rd))
#define VL_CONCAT_QQQ_TTT(obits, lbits, rbits, ld, rd) \
    (static_cast<QData>(ld) << (rbits) | static_cast<QData>(rd))

// clang-format off
#define VL_CONCAT_WII_GEN(outputSuffix) \
static inline WDataOutP VL_CONCAT_WII_##outputSuffix##TT( \
        int obits, int lbits, int rbits, WDataOutP const owp, IData ld, IData rd) VL_MT_SAFE { \
        *VL_GET_ELEM(outputSuffix, owp, 0) = rd; \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_EDATASIZE, VL_GET_ELEM(outputSuffix, owp, 1)); \
        _vl_insert_WI_##outputSuffix(owp, ld, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_CONCAT_WII_GEN)
#undef VL_CONCAT_WII_GEN

// clang-format off
#define VL_CONCAT_WWI_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_CONCAT_WWI_##outputSuffix##lhsSuffix##T( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, IData rd) \
        VL_MT_SAFE { \
        *VL_GET_ELEM(outputSuffix, owp, 0) = rd; \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_EDATASIZE, VL_GET_ELEM(outputSuffix, owp, 1)); \
        _vl_insert_WW_##outputSuffix##lhsSuffix(owp, lwp, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_CONCAT_WWI_GEN)
#undef VL_CONCAT_WWI_GEN

// clang-format off
#define VL_CONCAT_WIW_GEN(outputSuffix, rhsSuffix) \
static inline WDataOutP VL_CONCAT_WIW##outputSuffix##T##rhsSuffix( \
        int obits, int lbits, int rbits, WDataOutP owp, IData ld, WDataInP const rwp) \
        VL_MT_SAFE { \
        const int rwords = VL_WORDS_I(rbits); \
        VL_ASSIGN_W_##outputSuffix##rhsSuffix(rbits, owp, rwp); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - rbits, VL_GET_ELEM(outputSuffix, owp, rwords)); \
        _vl_insert_WI_##outputSuffix(owp, ld, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_CONCAT_WIW_GEN)
#undef VL_CONCAT_WIW_GEN

// clang-format off
#define VL_CONCAT_WIQ_GEN(outputSuffix) \
static inline WDataOutP VL_CONCAT_WIQ_##outputSuffix##TT( \
        int obits, int lbits, int rbits, WDataOutP owp, IData ld, QData rd) VL_MT_SAFE { \
        VL_SET_WQ_##outputSuffix(owp, rd); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_QUADSIZE, \
                                 VL_GET_ELEM(outputSuffix, owp, VL_WQ_WORDS_E)); \
        _vl_insert_WI_##outputSuffix(owp, ld, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_CONCAT_WIQ_GEN)
#undef VL_CONCAT_WIQ_GEN

// clang-format off
#define VL_CONCAT_WQI_GEN(outputSuffix) \
static inline WDataOutP VL_CONCAT_WQI_##outputSuffix##TT( \
        int obits, int lbits, int rbits, WDataOutP owp, QData ld, IData rd) VL_MT_SAFE { \
        *VL_GET_ELEM(outputSuffix, owp, 0) = rd; \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_EDATASIZE, VL_GET_ELEM(outputSuffix, owp, 1)); \
        _vl_insert_WQ_##outputSuffix(owp, ld, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_CONCAT_WQI_GEN)
#undef VL_CONCAT_WQI_GEN

// clang-format off
#define VL_CONCAT_WQQ_GEN(outputSuffix) \
static inline WDataOutP VL_CONCAT_WQQ_##outputSuffix##TT( \
        int obits, int lbits, int rbits, WDataOutP owp, QData ld, QData rd) VL_MT_SAFE { \
        VL_SET_WQ_##outputSuffix(owp, rd); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_QUADSIZE, \
                                 VL_GET_ELEM(outputSuffix, owp, VL_WQ_WORDS_E)); \
        _vl_insert_WQ_##outputSuffix(owp, ld, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_CONCAT_WQQ_GEN)
#undef VL_CONCAT_WQQ_GEN

// clang-format off
#define VL_CONCAT_WWQ_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_CONCAT_WWQ_##outputSuffix##lhsSuffix##T( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, QData rd) \
        VL_MT_SAFE { \
        VL_SET_WQ_##outputSuffix(owp, rd); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - VL_QUADSIZE, \
                                 VL_GET_ELEM(outputSuffix, owp, VL_WQ_WORDS_E)); \
        _vl_insert_WW_##outputSuffix##lhsSuffix(owp, lwp, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_CONCAT_WWQ_GEN)
#undef VL_CONCAT_WWQ_GEN

// clang-format off
#define VL_CONCAT_WQW_GEN(outputSuffix, rhsSuffix) \
static inline WDataOutP VL_CONCAT_WQW_##outputSuffix##T##rhsSuffix(int obits, int lbits, int rbits, WDataOutP owp, QData ld, \
                                      WDataInP const rwp) VL_MT_SAFE { \
    const int rwords = VL_WORDS_I(rbits); \
    VL_ASSIGN_W_##outputSuffix##rhsSuffix(rbits, owp, rwp); \
    VL_ZERO_OFFSET_W_##outputSuffix(obits - rbits, VL_GET_ELEM(outputSuffix, owp, rwords)); \
    _vl_insert_WQ_##outputSuffix(owp, ld, rbits + lbits - 1, rbits); \
    return owp; \
}
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_CONCAT_WQW_GEN)
#undef VL_CONCAT_WQW_GEN

// clang-format off
#define VL_CONCAT_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_CONCAT_WWW_##outputSuffix##lhsSuffix##rhsSuffix( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, WDataInP const rwp) \
        VL_MT_SAFE { \
        const int rwords = VL_WORDS_I(rbits); \
        VL_ASSIGN_W_##outputSuffix##rhsSuffix(rbits, owp, rwp); \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - rbits, VL_GET_ELEM(outputSuffix, owp, rwords)); \
        _vl_insert_WW_##outputSuffix##lhsSuffix(owp, lwp, rbits + lbits - 1, rbits); \
        return owp; \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_CONCAT_WWW_GEN)
#undef VL_CONCAT_WWW_GEN

//===================================================================
// Shifts

// Static shift, used by internal functions
// The output is the same as the input - it overlaps!
static inline void _vl_shiftl_inplace_w(int obits, WDataOutP iowp,
                                        IData rd /*1 or 4*/) VL_MT_SAFE {
    const int words = VL_WORDS_I(obits);
    const EData linsmask = VL_MASK_E(rd);
    for (int i = words - 1; i >= 1; --i) {
        iowp[i]
            = ((iowp[i] << rd) & ~linsmask) | ((iowp[i - 1] >> (VL_EDATASIZE - rd)) & linsmask);
    }
    iowp[0] = ((iowp[0] << rd) & ~linsmask);
    iowp[VL_WORDS_I(obits) - 1] &= VL_MASK_E(obits);
}

// EMIT_RULE: VL_SHIFTL:  oclean=lclean; rclean==clean;
// Important: Unlike most other funcs, the shift might well be a computed
// expression.  Thus consider this when optimizing.  (And perhaps have 2 funcs?)
// If RHS (rd/rwp) is larger than the output, zeros (or all ones for >>>) must be returned
// (This corresponds to AstShift*Ovr Ast nodes)
static inline IData VL_SHIFTL_III_TTT(int /*obits*/, int, int, IData lhs, IData rhs) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs >= VL_IDATASIZE)) return 0;
    return lhs << rhs;  // Small is common so not clean return
}
static inline IData VL_SHIFTL_IIQ_TTT(int obits, int, int, IData lhs, QData rhs) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs >= VL_IDATASIZE)) return 0;
    return VL_CLEAN_II(obits, obits, lhs << rhs);
}
static inline QData VL_SHIFTL_QQI_TTT(int /*obits*/, int, int, QData lhs, IData rhs) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs >= VL_QUADSIZE)) return 0;
    return lhs << rhs;  // Small is common so not clean return
}
static inline QData VL_SHIFTL_QQQ_TTT(int obits, int, int, QData lhs, QData rhs) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs >= VL_QUADSIZE)) return 0;
    return VL_CLEAN_QQ(obits, obits, lhs << rhs);
}

// clang-format off
#define VL_SHIFTL_WWI_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SHIFTL_WWI_##outputSuffix##lhsSuffix##T( \
        int obits, int, int, WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        const int word_shift = VL_BITWORD_E(rd); \
        const int bit_shift = VL_BITBIT_E(rd); \
        if (rd >= static_cast<IData>(obits)) { /* rd may be huge with MSB set */ \
            for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
        } else if (bit_shift == 0) { /* Aligned word shift (<<0,<<32,<<64 etc) */ \
            for (int i = 0; i < word_shift; ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix); \
            for (int i = word_shift; i < VL_WORDS_I(obits); ++i) { \
                *owp = *lwp; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
            } \
        } else { \
            for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            _vl_insert_WW_##outputSuffix##lhsSuffix(resultp, lwp, obits - 1, rd); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SHIFTL_WWI_GEN)
#undef VL_SHIFTL_WWI_GEN

// clang-format off
#define VL_SHIFTL_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_SHIFTL_WWW_##outputSuffix##lhsSuffix##rhsSuffix(int obits, int lbits, int rbits, WDataOutP owp, \
                                          WDataInP const lwp, WDataInP rwp) VL_MT_SAFE { \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            if (VL_UNLIKELY(*rwp)) { /* Huge shift 1>>32 or more */ \
                return VL_ZERO_W_##outputSuffix(obits, owp); \
            } \
            rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return VL_SHIFTL_WWI_##outputSuffix##lhsSuffix##T(obits, lbits, 32, owp, lwp, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_SHIFTL_WWW_GEN)
#undef VL_SHIFTL_WWW_GEN

// clang-format off
#define VL_SHIFTL_WWQ_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SHIFTL_WWQ_##outputSuffix##lhsSuffix##T(int obits, int lbits, int rbits, WDataOutP owp, \
                                          WDataInP const lwp, QData rd) VL_MT_SAFE { \
        if (VL_UNLIKELY(rd >> VL_IDATASIZE)) return VL_ZERO_W_##outputSuffix(obits, owp); \
        return VL_SHIFTL_WWI_##outputSuffix##lhsSuffix##T(obits, lbits, 32, owp, lwp, static_cast<IData>(rd)); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SHIFTL_WWQ_GEN)
#undef VL_SHIFTL_WWQ_GEN

// clang-format off
#define VL_SHIFTL_IIW_GEN(rhsSuffix) \
static inline IData VL_SHIFTL_IIW_TT##rhsSuffix(int obits, int, int rbits, IData lhs, WDataInP rwp) \
        VL_MT_SAFE { \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            if (VL_UNLIKELY(*rwp)) { /* Huge shift 1>>32 or more */ \
                return 0; \
            } \
            rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return VL_SHIFTL_III_TTT(obits, obits, 32, lhs, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SHIFTL_IIW_GEN)
#undef VL_SHIFTL_IIW_GEN

// clang-format off
#define VL_SHIFTL_QQW_GEN(rhsSuffix) \
static inline QData VL_SHIFTL_QQW_TT##rhsSuffix(int obits, int, int rbits, QData lhs, WDataInP rwp) \
        VL_MT_SAFE { \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            if (VL_UNLIKELY(*rwp)) { /* Huge shift 1>>32 or more */ \
                return 0; \
            } \
            rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        /* Above checks rwp[1]==0 so not needed in below shift */ \
        return VL_SHIFTL_QQI_TTT(obits, obits, 32, lhs, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SHIFTL_QQW_GEN)
#undef VL_SHIFTL_QQW_GEN

// EMIT_RULE: VL_SHIFTR:  oclean=lclean; rclean==clean;
// Important: Unlike most other funcs, the shift might well be a computed
// expression.  Thus consider this when optimizing.  (And perhaps have 2 funcs?)
static inline IData VL_SHIFTR_III_TTT(int /*obits*/, int, int, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs >= VL_IDATASIZE)) return 0;
    return lhs >> rhs;
}
static inline IData VL_SHIFTR_IIQ_TTT(int /*obits*/, int, int, IData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs >= VL_IDATASIZE)) return 0;
    return lhs >> rhs;
}
static inline QData VL_SHIFTR_QQI_TTT(int /*obits*/, int, int, QData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs >= VL_QUADSIZE)) return 0;
    return lhs >> rhs;
}
static inline QData VL_SHIFTR_QQQ_TTT(int /*obits*/, int, int, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs >= VL_QUADSIZE)) return 0;
    return lhs >> rhs;
}

// clang-format off
#define VL_SHIFTR_WWI_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SHIFTR_WWI_##outputSuffix##lhsSuffix##T( \
        int obits, int, int, WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE { \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        const int word_shift = VL_BITWORD_E(rd); /* Maybe 0 */ \
        const int bit_shift = VL_BITBIT_E(rd); \
        if (rd >= static_cast<IData>(obits)) { /* rd may be huge with MSB set */ \
            for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
        } else if (bit_shift == 0) { /* Aligned word shift (>>0,>>32,>>64 etc) */ \
            const int copy_words = (VL_WORDS_I(obits) - word_shift); \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix) + (word_shift * VL_GET_TYPE_JUMP(lhsSuffix)); \
            for (int i = 0; i < copy_words; ++i) { \
                *owp = *lwp; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
            } \
            for (int i = copy_words; i < VL_WORDS_I(obits); ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
        } else { \
            const int loffset = rd & VL_SIZEBITS_E; \
            /* bits that end up in lword (know loffset!=0) Middle words */ \
            const int nbitsonright = VL_EDATASIZE - loffset; \
            const int words = VL_WORDS_I(obits - rd); \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix) + (word_shift * VL_GET_TYPE_JUMP(lhsSuffix)); \
            for (int i = 0; i < words; ++i) { \
                *owp = *lwp >> loffset; \
                const int upperword = i + word_shift + 1; \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
                if (upperword < VL_WORDS_I(obits)) *owp |= *lwp << nbitsonright; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            for (int i = words; i < VL_WORDS_I(obits); ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SHIFTR_WWI_GEN)
#undef VL_SHIFTR_WWI_GEN

// clang-format off
#define VL_SHIFTR_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_SHIFTR_WWW_##outputSuffix##lhsSuffix##rhsSuffix( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, WDataInP rwp) \
        VL_MT_SAFE { \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            if (VL_UNLIKELY(*rwp)) { /* Huge shift 1>>32 or more */ \
                return VL_ZERO_W_##outputSuffix(obits, owp); \
            } \
            rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return VL_SHIFTR_WWI_##outputSuffix##lhsSuffix##T(obits, lbits, 32, owp, lwp, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_SHIFTR_WWW_GEN)
#undef VL_SHIFTR_WWW_GEN

// clang-format off
#define VL_SHIFTR_WWQ_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SHIFTR_WWQ_##outputSuffix##lhsSuffix##T( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, QData rd) \
        VL_MT_SAFE { \
        if (VL_UNLIKELY(rd >> VL_IDATASIZE)) return VL_ZERO_W_##outputSuffix(obits, owp); \
        return VL_SHIFTR_WWI_##outputSuffix##lhsSuffix##T(obits, lbits, rbits, owp, lwp, static_cast<IData>(rd)); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SHIFTR_WWQ_GEN)
#undef VL_SHIFTR_WWQ_GEN

// clang-format off
#define VL_SHIFTR_IIW_GEN(rhsSuffix) \
static inline IData VL_SHIFTR_IIW_TT##rhsSuffix(int obits, int, int rbits, IData lhs, \
                                                    WDataInP rwp) VL_PURE { \
        rwp = rwp + VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp = rwp + VL_GET_TYPE_JUMP(rhsSuffix); \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            if (VL_UNLIKELY(*rwp)) return 0; /* Huge shift 1>>32 or more */ \
            rwp = rwp + VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return VL_SHIFTR_III_TTT(obits, obits, 32, lhs, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SHIFTR_IIW_GEN)
#undef VL_SHIFTR_IIW_GEN

// clang-format off
#define VL_SHIFTR_QQW_GEN(rhsSuffix) \
static inline QData VL_SHIFTR_QQW_TT##rhsSuffix(int obits, int, int rbits, QData lhs, \
                                                    WDataInP rwp) VL_PURE { \
        rwp = rwp + VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp = rwp + VL_GET_TYPE_JUMP(rhsSuffix); \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            if (VL_UNLIKELY(*rwp)) return 0; /* Huge shift 1>>32 or more */ \
            rwp = rwp + VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        return VL_SHIFTR_QQI_TTT(obits, obits, 32, lhs, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SHIFTR_QQW_GEN)
#undef VL_SHIFTR_QQW_GEN

// EMIT_RULE: VL_SHIFTRS:  oclean=false; lclean=clean, rclean==clean;
static inline IData VL_SHIFTRS_III_TTT(int obits, int lbits, int, IData lhs, IData rhs) VL_PURE {
    // Note the C standard does not specify the >> operator as a arithmetic shift!
    // IEEE says signed if output signed, but bit position from lbits;
    // must use lbits for sign; lbits might != obits,
    // an EXTEND(SHIFTRS(...)) can became a SHIFTRS(...) within same 32/64 bit word length
    const IData sign = -(lhs >> (lbits - 1));  // ffff_ffff if negative
    if (VL_UNLIKELY(rhs >= VL_IDATASIZE)) return sign & VL_MASK_I(obits);
    const IData signext = ~(VL_MASK_I(lbits) >> rhs);  // One with bits where we've shifted "past"
    return (lhs >> rhs) | (sign & VL_CLEAN_II(obits, obits, signext));
}
static inline QData VL_SHIFTRS_QQI_TTT(int obits, int lbits, int, QData lhs, IData rhs) VL_PURE {
    const QData sign = -(lhs >> (lbits - 1));
    if (VL_UNLIKELY(rhs >= VL_QUADSIZE)) return sign & VL_MASK_Q(obits);
    const QData signext = ~(VL_MASK_Q(lbits) >> rhs);
    return (lhs >> rhs) | (sign & VL_CLEAN_QQ(obits, obits, signext));
}
static inline IData VL_SHIFTRS_IQI_TTT(int obits, int lbits, int rbits, QData lhs,
                                       IData rhs) VL_PURE {
    return static_cast<IData>(VL_SHIFTRS_QQI_TTT(obits, lbits, rbits, lhs, rhs));
}

// clang-format off
#define VL_SHIFTRS_WWI_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SHIFTRS_WWI_##outputSuffix##lhsSuffix##T( \
        int obits, int lbits, int, WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE { \
        const int word_shift = VL_BITWORD_E(rd); \
        const int bit_shift = VL_BITBIT_E(rd); \
        const int lmsw = VL_WORDS_I(obits) - 1; \
        const EData sign = VL_SIGNONES_E(lbits, *VL_GET_ELEM(lhsSuffix, lwp, lmsw)); \
        const WDataOutP resultp = owp; \
        owp += VL_GET_TYPE_OFFSET(outputSuffix); \
        if (rd >= static_cast<IData>(obits)) { /* Shifting past end, sign in all of lbits */ \
            for (int i = 0; i < lmsw; ++i) { \
                *owp = sign; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            *owp = sign & VL_MASK_E(lbits); \
        } else if (bit_shift == 0) { /* Aligned word shift (>>0,>>32,>>64 etc) */ \
            const int copy_words = (VL_WORDS_I(obits) - word_shift); \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix) + (word_shift * VL_GET_TYPE_JUMP(lhsSuffix)); \
            for (int i = 0; i < copy_words; ++i) { \
                *owp = *lwp; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
            } \
            if (copy_words >= 0) *(owp - VL_GET_TYPE_JUMP(outputSuffix)) |= ~VL_MASK_E(obits) & sign; \
            for (int i = copy_words; i < VL_WORDS_I(obits); ++i) { \
                *owp = sign; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            *(owp - VL_GET_TYPE_JUMP(outputSuffix)) &= VL_MASK_E(lbits); \
        } else { \
            const int loffset = rd & VL_SIZEBITS_E; \
            const int nbitsonright \
                = VL_EDATASIZE - loffset; /* bits that end up in lword (know loffset!=0) */ \
            /* Middle words */ \
            const int words = VL_WORDS_I(obits - rd); \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix) + (word_shift * VL_GET_TYPE_JUMP(lhsSuffix)); \
            for (int i = 0; i < words; ++i) { \
                *owp = *lwp >> loffset; \
                const int upperword = i + word_shift + 1; \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
                if (upperword < VL_WORDS_I(obits)) *owp |= *lwp << nbitsonright; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            if (words) *(owp - VL_GET_TYPE_JUMP(outputSuffix)) |= sign & ~VL_MASK_E(obits - loffset); \
            for (int i = words; i < VL_WORDS_I(obits); ++i) { \
                *owp = sign; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            *(owp - VL_GET_TYPE_JUMP(outputSuffix)) &= VL_MASK_E(lbits); \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SHIFTRS_WWI_GEN)
#undef VL_SHIFTRS_WWI_GEN

// clang-format off
#define VL_SHIFTRS_WWW_GEN(outputSuffix, lhsSuffix, rhsSuffix) \
static inline WDataOutP VL_SHIFTRS_WWW_##outputSuffix##lhsSuffix##rhsSuffix( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, WDataInP rwp) \
        VL_MT_SAFE { \
        rwp += VL_GET_TYPE_OFFSET(rhsSuffix); \
        const EData rwp0 = *rwp; \
        rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        EData overshift = 0; /* Huge shift 1>>32 or more */ \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) { \
            overshift |= *rwp; \
            rwp += VL_GET_TYPE_JUMP(rhsSuffix); \
        } \
        if (VL_UNLIKELY(overshift || rwp0 >= static_cast<IData>(obits))) { \
            const int owords = VL_WORDS_I(obits); \
            if (VL_SIGN_E_T(lbits, *VL_GET_ELEM(lhsSuffix, lwp, owords - 1))) { \
                VL_MEMSET_ONES_W(owp, owords); \
                *VL_GET_ELEM(outputSuffix, owp, owords - 1) &= VL_MASK_E(lbits); \
            } else { \
                VL_MEMSET_ZERO_W(owp, owords); \
            } \
            return owp; \
        } \
        return VL_SHIFTRS_WWI_##outputSuffix##lhsSuffix##T(obits, lbits, 32, owp, lwp, rwp0); \
    }
// clang-format on
VL_GEN_HELPER_THREE_ARG(VL_SHIFTRS_WWW_GEN)
#undef VL_SHIFTRS_WWW_GEN

// clang-format off
#define VL_SHIFTRS_WWQ_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SHIFTRS_WWQ_##outputSuffix##lhsSuffix##T( \
        int obits, int lbits, int rbits, WDataOutP owp, WDataInP const lwp, QData rd) \
        VL_MT_SAFE { \
        VlWide<VL_WQ_WORDS_E> rwp; \
        VL_SET_WQ_T(rwp, rd); \
        return VL_SHIFTRS_WWW_##outputSuffix##lhsSuffix##T(obits, lbits, rbits, owp, lwp, rwp); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SHIFTRS_WWQ_GEN)
#undef VL_SHIFTRS_WWQ_GEN

// clang-format off
#define VL_SHIFTRS_IIW_GEN(rhsSuffix) \
static inline IData VL_SHIFTRS_IIW_TT##rhsSuffix(int obits, int lbits, int rbits, IData lhs, \
                                                     WDataInP const rwp) VL_PURE { \
        EData overshift = 0; /* Huge shift 1>>32 or more */ \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) overshift |= rwp[i]; \
        if (VL_UNLIKELY(overshift || rwp[0] >= static_cast<IData>(obits))) { \
            const IData sign = -(lhs >> (lbits - 1)); /* ffff_ffff if negative */ \
            return VL_CLEAN_II(obits, obits, sign); \
        } \
        return VL_SHIFTRS_III_TTT(obits, lbits, 32, lhs, rwp[0]); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SHIFTRS_IIW_GEN)
#undef VL_SHIFTRS_IIW_GEN

// clang-format off
#define VL_SHIFTRS_QQW_GEN(rhsSuffix) \
static inline QData VL_SHIFTRS_QQW_TT##rhsSuffix(int obits, int lbits, int rbits, QData lhs, \
                                                     WDataInP const rwp) VL_PURE { \
        EData overshift = 0; /* Huge shift 1>>32 or more */ \
        for (int i = 1; i < VL_WORDS_I(rbits); ++i) overshift |= rwp[i]; \
        if (VL_UNLIKELY(overshift || rwp[0] >= static_cast<IData>(obits))) { \
            const QData sign = -(lhs >> (lbits - 1)); /* ffff_ffff if negative */ \
            return VL_CLEAN_QQ(obits, obits, sign); \
        } \
        return VL_SHIFTRS_QQI_TTT(obits, lbits, 32, lhs, rwp[0]); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SHIFTRS_QQW_GEN)
#undef VL_SHIFTRS_QQW_GEN

static inline IData VL_SHIFTRS_IIQ_TTT(int obits, int lbits, int rbits, IData lhs,
                                       QData rhs) VL_PURE {
    VlWide<VL_WQ_WORDS_E> rwp;
    VL_SET_WQ_T(rwp, rhs);
    return VL_SHIFTRS_IIW_TTT(obits, lbits, rbits, lhs, rwp);
}
static inline QData VL_SHIFTRS_QQQ_TTT(int obits, int lbits, int rbits, QData lhs,
                                       QData rhs) VL_PURE {
    VlWide<VL_WQ_WORDS_E> rwp;
    VL_SET_WQ_T(rwp, rhs);
    return VL_SHIFTRS_QQW_TTT(obits, lbits, rbits, lhs, rwp);
}

//===================================================================
// Bit selection

// EMIT_RULE: VL_BITSEL:  oclean=dirty; rclean==clean;
#define VL_BITSEL_IIII_TTTT(lbits, lhs, rhs) ((lhs) >> (rhs))
#define VL_BITSEL_QIII_TTTT(lbits, lhs, rhs) ((lhs) >> (rhs))
#define VL_BITSEL_QQII_TTTT(lbits, lhs, rhs) ((lhs) >> (rhs))
#define VL_BITSEL_IQII_TTTT(lbits, lhs, rhs) (static_cast<IData>((lhs) >> (rhs)))

// clang-format off
#define VL_BITSEL_IWII_GEN(lhsSuffix) \
static inline IData VL_BITSEL_IWII_T##lhsSuffix##TT(int lbits, WDataInP const lwp, IData rd) \
        VL_MT_SAFE { \
        const int word = VL_BITWORD_E(rd); \
        if (VL_UNLIKELY(rd >= static_cast<IData>(lbits))) { \
            VL_IF_VX(lhsSuffix, \
                     VL_FATAL_MT(__FILE__, __LINE__, "", \
                                 "Tried to access index out of range - Verilator shall handle " \
                                 "index ranges at compile time");); \
            VL_IF_T(lhsSuffix, return ~0;); /* Spec says you can go outside the range of a array. \
                                               Don't coredump if so. */ \
            /* We return all 1's as that's more likely to find bugs (?) than 0's. */ \
        } \
        return (*VL_GET_ELEM(lhsSuffix, lwp, word) >> VL_BITBIT_E(rd)); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_BITSEL_IWII_GEN)
#undef VL_BITSEL_IWII_GEN

// EMIT_RULE: VL_RANGE:  oclean=lclean;  out=dirty
// <msb> & <lsb> MUST BE CLEAN (currently constant)
#define VL_SEL_IIII_TTTT(lbits, lhs, lsb, width) ((lhs) >> (lsb))
#define VL_SEL_QQII_TTTT(lbits, lhs, lsb, width) ((lhs) >> (lsb))
#define VL_SEL_IQII_TTTT(lbits, lhs, lsb, width) (static_cast<IData>((lhs) >> (lsb)))

// #define VL_SEL_IRII(lbits, lhs, lsb, width) ((lhs) >> (lsb))
template <typename T>
static inline IData VL_SEL_IRII_TTTT(int lbits, const VlQueue<T>& lhs, IData lsb,
                                     IData width) VL_MT_SAFE {
    IData val = 0;
    if (sizeof(T) == 8) {
        const int offset = lhs.size() * sizeof(T) / sizeof(IData) - VL_BITWORD_E(lsb) - 1;
        const int wordIndex = VL_BITWORD_E(VL_BITBIT_Q(lsb));
        const int shiftAmt = wordIndex << 5;
        const int index = offset / 2;
        val |= static_cast<IData>(lhs.at(index) >> shiftAmt);
        return val;
    }
    const int qElemPerWord = 4 / sizeof(T);
    const int shiftAmt = qElemPerWord > 1 ? sizeof(T) * 8 : 0;
    for (int ii = 0; ii < qElemPerWord; ii++) {
        const int offset = lhs.size() * sizeof(T) / sizeof(IData) - VL_BITWORD_E(lsb) - 1;
        const int index = offset * qElemPerWord + (qElemPerWord - 1 - ii);
        val |= static_cast<IData>(lhs.at(index)) << (shiftAmt * ii);
    }
    return val;
}

template <std::size_t N_Words>
static inline IData VL_SEL_IRII_TTTT(int lbits, const VlQueue<VlWide<N_Words>>& lhs, IData lsb,
                                     IData width) VL_MT_SAFE {
    IData val = 0;

    const int offset = lhs.size() * N_Words - VL_BITWORD_E(lsb) - 1;
    const int wordIndex = VL_BITWORD_E(lsb % (N_Words * 32));
    const int shiftAmt = VL_BITBIT_I(lsb);
    const int index = offset / N_Words;
    val = lhs.at(index).at(wordIndex) >> shiftAmt;

    return val;
}

// clang-format off
#define VL_SEL_IWII_GEN(lhsSuffix) \
static inline IData VL_SEL_IWII_T##lhsSuffix##TT(int lbits, WDataInP const lwp, IData lsb, \
                                                     IData width) VL_MT_SAFE { \
        const int msb = lsb + width - 1; \
        if (VL_UNLIKELY(msb >= lbits)) { \
            VL_IF_VX(lhsSuffix, \
                     VL_FATAL_MT(__FILE__, __LINE__, "", \
                                 "Tried to access index out of range - Verilator shall handle " \
                                 "index ranges at compile time");); \
            VL_IF_T(lhsSuffix, return ~0;); /* Spec says you can go outside the range of a array. \
                                    Don't coredump if so. */ \
        } \
        const int lsbWord = VL_BITWORD_E(lsb); \
        const IData lo = *VL_GET_ELEM(lhsSuffix, lwp, lsbWord) >> VL_BITBIT_E(lsb); \
        if (VL_BITWORD_E(msb) == lsbWord) return lo; \
        /* 32 bit extraction may span two words */ \
        const int nbitsfromlow \
            = VL_EDATASIZE - VL_BITBIT_E(lsb); /* bits that come from low word */ \
        return (*VL_GET_ELEM(lhsSuffix, lwp, VL_BITWORD_E(msb)) << nbitsfromlow) | lo; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SEL_IWII_GEN)
#undef VL_SEL_IWII_GEN

// clang-format off
#define VL_SEL_QWII_GEN(lhsSuffix) \
static inline QData VL_SEL_QWII_T##lhsSuffix##TT(int lbits, WDataInP const lwp, IData lsb, \
                                                     IData width) VL_MT_SAFE { \
        const int msb = lsb + width - 1; \
        if (VL_UNLIKELY(msb >= lbits)) { \
            VL_IF_VX(lhsSuffix, \
                     VL_FATAL_MT(__FILE__, __LINE__, "", \
                                 "Tried to access index out of range - Verilator shall handle " \
                                 "index ranges at compile time");); \
            VL_IF_T(lhsSuffix, return ~0;); /* Spec says you can go outside the range of a array. \
                          Don't coredump if so. */ \
        } \
        const int lsbWord = VL_BITWORD_E(lsb); \
        const IData lo = *VL_GET_ELEM(lhsSuffix, lwp, lsbWord) >> VL_BITBIT_E(lsb); \
        if (VL_BITWORD_E(msb) == lsbWord) return lo; \
        const int nbitsfromlow = VL_EDATASIZE - VL_BITBIT_E(lsb); \
        const QData hi = *VL_GET_ELEM(lhsSuffix, lwp, VL_BITWORD_E(msb)); \
        if (VL_BITWORD_E(msb) == 1 + lsbWord) return (hi << nbitsfromlow) | lo; \
        /* 64 bit extraction may span three words */ \
        const QData mid = *VL_GET_ELEM(lhsSuffix, lwp, VL_BITWORD_E(lsb) + 1); \
        return (hi << (nbitsfromlow + VL_EDATASIZE)) | (mid << nbitsfromlow) | lo; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SEL_QWII_GEN)
#undef VL_SEL_QWII_GEN

// clang-format off
#define VL_SEL_WWII_GEN(outputSuffix, lhsSuffix) \
static inline WDataOutP VL_SEL_WWII_##outputSuffix##lhsSuffix##TT( \
        int obits, int lbits, WDataOutP owp, WDataInP lwp, IData lsb, IData width) VL_MT_SAFE { \
        const int msb = lsb + width - 1; \
        const int word_shift = VL_BITWORD_E(lsb); \
        const WDataOutP resultp = owp; \
        if (VL_UNLIKELY(msb >= lbits)) { /* Outside bounds, */ \
            VL_IF_VX(lhsSuffix, \
                     VL_FATAL_MT(__FILE__, __LINE__, "", \
                                 "Tried to access index out of range - Verilator shall handle " \
                                 "index ranges at compile time");); \
            VL_IF_T(lhsSuffix, VL_ALLONES_W_##outputSuffix(obits, owp);); \
        } else if (VL_BITBIT_E(lsb) == 0) { \
            /* Just a word extract */ \
            owp += VL_GET_TYPE_OFFSET(outputSuffix); \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix) + (word_shift * VL_GET_TYPE_JUMP(lhsSuffix)); \
            for (int i = 0; i < VL_WORDS_I(obits); ++i) { \
                *owp = *lwp; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
            } \
        } else { \
            /* Not a _vl_insert because the bits come from any bit number and goto bit 0 */ \
            const int loffset = lsb & VL_SIZEBITS_E; \
            const int nbitsfromlow = VL_EDATASIZE - loffset; /* bits that end up in lword (know \
                                                                loffset!=0) Middle words */ \
            const int words = VL_WORDS_I(msb - lsb + 1); \
            owp += VL_GET_TYPE_OFFSET(outputSuffix); \
            lwp += VL_GET_TYPE_OFFSET(lhsSuffix) + (word_shift * VL_GET_TYPE_JUMP(lhsSuffix)); \
            for (int i = 0; i < words; ++i) { \
                *owp = *lwp >> loffset; \
                const int upperword = i + word_shift + 1; \
                lwp += VL_GET_TYPE_JUMP(lhsSuffix); \
                if (upperword <= static_cast<int>(VL_BITWORD_E(msb))) { \
                    *owp |= *lwp << nbitsfromlow; \
                } \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
            for (int i = words; i < VL_WORDS_I(obits); ++i) { \
                *owp = 0; \
                owp += VL_GET_TYPE_JUMP(outputSuffix); \
            } \
        } \
        return resultp; \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SEL_WWII_GEN)
#undef VL_SEL_WWII_GEN

template <typename T>
static inline VlQueue<T> VL_CLONE_Q(const VlQueue<T>& from, int lbits, int srcElementBits,
                                    int dstElementBits) {
    VlQueue<T> ret;
    VL_COPY_Q(ret, from, lbits, srcElementBits, dstElementBits);
    return ret;
}

template <typename T>
static inline VlQueue<T> VL_REVCLONE_Q(const VlQueue<T>& from, int lbits, int srcElementBits,
                                       int dstElementBits) {
    VlQueue<T> ret;
    VL_REVCOPY_Q(ret, from, lbits, srcElementBits, dstElementBits);
    return ret;
}

// Helper function to get a bit from a queue at a specific bit index
template <typename T>
static inline bool VL_GET_QUEUE_BIT(const VlQueue<T>& queue, int srcElementBits, size_t bitIndex) {
    const size_t elemIdx = bitIndex / srcElementBits;
    if (VL_UNLIKELY(elemIdx >= queue.size())) return false;

    const T element = queue.at(elemIdx);
    if (srcElementBits == 1) return element & 1;

    const size_t bitInElem = bitIndex % srcElementBits;
    const size_t actualBitPos = srcElementBits - 1 - bitInElem;
    return (element >> actualBitPos) & 1;
}

// Helper function to set a bit in the destination queue
template <typename T>
static inline void VL_SET_QUEUE_BIT(VlQueue<T>& queue, int dstElementBits, size_t bitIndex,
                                    bool value) {
    if (dstElementBits == 1) {
        if (VL_UNLIKELY(bitIndex >= queue.size())) return;
        queue.atWrite(bitIndex) = value ? 1 : 0;
    } else {
        const size_t elemIdx = bitIndex / dstElementBits;
        if (VL_UNLIKELY(elemIdx >= queue.size())) return;
        const size_t bitInElem = bitIndex % dstElementBits;
        const size_t actualBitPos = dstElementBits - 1 - bitInElem;
        if (value) {
            queue.atWrite(elemIdx) |= (static_cast<T>(1) << actualBitPos);
        } else {
            queue.atWrite(elemIdx) &= ~(static_cast<T>(1) << actualBitPos);
        }
    }
}

// Helper function to get a bit from a VlWide queue at a specific bit index
template <std::size_t N_Words>
static inline bool VL_GET_QUEUE_BIT(const VlQueue<VlWide<N_Words>>& queue, int srcElementBits,
                                    size_t bitIndex) {
    const size_t elemIdx = bitIndex / srcElementBits;
    if (VL_UNLIKELY(elemIdx >= queue.size())) return false;

    const VlWide<N_Words>& element = queue.at(elemIdx);
    const size_t bitInElem = bitIndex % srcElementBits;
    const size_t actualBitPos = srcElementBits - 1 - bitInElem;

    return VL_BITISSET_W(element.data(), actualBitPos);
}

// Helper function to set a bit in a VlWide queue at a specific bit index
template <std::size_t N_Words>
static inline void VL_SET_QUEUE_BIT(VlQueue<VlWide<N_Words>>& queue, int dstElementBits,
                                    size_t bitIndex, bool value) {
    const size_t elemIdx = bitIndex / dstElementBits;
    if (VL_UNLIKELY(elemIdx >= queue.size())) return;

    const size_t bitInElem = bitIndex % dstElementBits;
    const size_t actualBitPos = dstElementBits - 1 - bitInElem;

    VlWide<N_Words>& element = queue.atWrite(elemIdx);
    if (value) {
        VL_ASSIGNBIT_WO(actualBitPos, element);
    } else {
        VL_ASSIGNBIT_WI(actualBitPos, element, 0);
    }
}

template <typename T>
static inline void VL_ZERO_INIT_QUEUE_ELEM(T& elem) {
    elem = 0;
}

template <std::size_t N_Words>
static inline void VL_ZERO_INIT_QUEUE_ELEM(VlWide<N_Words>& elem) {
    for (size_t j = 0; j < N_Words; ++j) { elem.at(j) = 0; }
}

// This specialization works for both VlQueue<CData> (and similar) as well
// as VlQueue<VlWide<N>>.
template <typename T>
static inline void VL_COPY_Q(VlQueue<T>& q, const VlQueue<T>& from, int /*lbits*/,
                             int srcElementBits, int dstElementBits) {
    if (srcElementBits == dstElementBits) {
        // Simple case: same element bit width, direct copy of each element
        if (VL_UNLIKELY(&q == &from)) return;  // Skip self-assignment when it's truly a no-op
        q = from;
    } else {
        // Different element bit widths: use streaming conversion
        VlQueue<T> srcCopy = from;
        const size_t srcTotalBits = from.size() * srcElementBits;
        const size_t dstSize = (srcTotalBits + dstElementBits - 1) / dstElementBits;
        q.renew(dstSize);
        for (size_t i = 0; i < dstSize; ++i) { VL_ZERO_INIT_QUEUE_ELEM(q.atWrite(i)); }
        for (size_t bitIndex = 0; bitIndex < srcTotalBits; ++bitIndex) {
            VL_SET_QUEUE_BIT(q, dstElementBits, bitIndex,
                             VL_GET_QUEUE_BIT(srcCopy, srcElementBits, bitIndex));
        }
    }
}

// This specialization works for both VlQueue<CData> (and similar) as well
// as VlQueue<VlWide<N>>.
template <typename T>
static inline void VL_REVCOPY_Q(VlQueue<T>& q, const VlQueue<T>& from, int lbits,
                                int srcElementBits, int dstElementBits) {
    const size_t srcTotalBits = from.size() * srcElementBits;
    const size_t dstSize = (srcTotalBits + dstElementBits - 1) / dstElementBits;

    // Always make a copy to handle the case where q and from are the same queue
    VlQueue<T> srcCopy = from;

    // Initialize all elements to zero using appropriate method
    q.renew(dstSize);
    for (size_t i = 0; i < dstSize; ++i) VL_ZERO_INIT_QUEUE_ELEM(q.atWrite(i));

    if (lbits == 1) {
        // Simple bit reversal: write directly to destination
        for (int i = srcTotalBits - 1; i >= 0; --i) {
            VL_SET_QUEUE_BIT(q, dstElementBits, srcTotalBits - 1 - i,
                             VL_GET_QUEUE_BIT(srcCopy, srcElementBits, i));
        }
    } else {
        // Generalized block-reversal for lbits > 1:
        // 1. Reverse all bits using 1-bit blocks
        // 2. Split into lbits-sized blocks and pad incomplete blocks on the left
        // 3. Reverse each lbits-sized block using 1-bit blocks
        const size_t numCompleteBlocks = srcTotalBits / lbits;
        const size_t remainderBits = srcTotalBits % lbits;
        const size_t srcBlocks = numCompleteBlocks + (remainderBits > 0 ? 1 : 0);

        size_t dstBitIndex = 0;

        for (size_t block = 0; block < srcBlocks; ++block) {
            const size_t blockStart = block * lbits;
            const int bitsToProcess = VL_LIKELY(block < numCompleteBlocks) ? lbits : remainderBits;
            for (int bit = bitsToProcess - 1; bit >= 0; --bit) {
                const size_t reversedBitIndex = blockStart + bit;
                const size_t originalBitIndex = srcTotalBits - 1 - reversedBitIndex;
                VL_SET_QUEUE_BIT(q, dstElementBits, dstBitIndex++,
                                 VL_GET_QUEUE_BIT(srcCopy, srcElementBits, originalBitIndex));
            }
            dstBitIndex += lbits - bitsToProcess;
        }
    }
}

// Reverse element order of an unpacked array in-place.
// Used by emitter for descending-range arrays after VL_UNPACK_*.
template <typename T_Value, std::size_t N_Depth>
static inline void VL_UNPACK_REVERSED(VlUnpacked<T_Value, N_Depth>& q) {
    for (size_t i = 0; i < N_Depth / 2; ++i) {
        const T_Value tmp = q[i];
        q[i] = q[N_Depth - 1 - i];
        q[N_Depth - 1 - i] = tmp;
    }
}

// Return a reversed copy of an unpacked array.
// Used by emitter for descending-range arrays before VL_PACK_*.
template <typename T_Value, std::size_t N_Depth>
static inline VlUnpacked<T_Value, N_Depth>
VL_PACK_REVERSED(const VlUnpacked<T_Value, N_Depth>& q) {
    VlUnpacked<T_Value, N_Depth> ret;
    for (size_t i = 0; i < N_Depth; ++i) ret[i] = q[N_Depth - 1 - i];
    return ret;
}

// Overloads for VlUnpacked source -> VlQueue destination
template <typename T, std::size_t N_Depth>
static inline void VL_COPY_Q(VlQueue<T>& q, const VlUnpacked<T, N_Depth>& from, int lbits,
                             int srcElementBits, int dstElementBits) {
    VlQueue<T> srcQ;
    srcQ.renew(N_Depth);
    for (size_t i = 0; i < N_Depth; ++i) srcQ.atWrite(i) = from[i];
    VL_COPY_Q(q, srcQ, lbits, srcElementBits, dstElementBits);
}

template <typename T, std::size_t N_Depth>
static inline void VL_REVCOPY_Q(VlQueue<T>& q, const VlUnpacked<T, N_Depth>& from, int lbits,
                                int srcElementBits, int dstElementBits) {
    VlQueue<T> srcQ;
    srcQ.renew(N_Depth);
    for (size_t i = 0; i < N_Depth; ++i) srcQ.atWrite(i) = from[N_Depth - 1 - i];
    VL_COPY_Q(q, srcQ, lbits, srcElementBits, dstElementBits);
}

//======================================================================
// Expressions needing insert/select

static inline void VL_UNPACK_RI_I(int lbits, int rbits, VlQueue<CData>& q, IData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RI_I(int lbits, int rbits, VlQueue<SData>& q, IData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RI_I(int lbits, int rbits, VlQueue<IData>& q, IData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RI_Q(int lbits, int rbits, VlQueue<CData>& q, QData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RI_Q(int lbits, int rbits, VlQueue<SData>& q, QData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RI_Q(int lbits, int rbits, VlQueue<IData>& q, QData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RQ_Q(int lbits, int rbits, VlQueue<QData>& q, QData from) {
    const size_t size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const QData mask = VL_MASK_Q(lbits);
    for (size_t i = 0; i < size; ++i) q.atWrite(size - 1 - i) = (from >> (i * lbits)) & mask;
}

static inline void VL_UNPACK_RI_W(int lbits, int rbits, VlQueue<CData>& q, WDataInP rwp) {
    const int size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) {
        // Extract from MSB to LSB: MSB goes to index 0
        const int bitPos = rbits - (i + 1) * lbits;
        const int actualBitPos = (bitPos < 0) ? 0 : bitPos;
        const int actualWidth = (bitPos < 0) ? (lbits + bitPos) : lbits;
        q.atWrite(i) = VL_SEL_IWII_TTTT(rbits, rwp, actualBitPos, actualWidth) & mask;
    }
}

static inline void VL_UNPACK_RI_W(int lbits, int rbits, VlQueue<SData>& q, WDataInP rwp) {
    const int size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) {
        // Extract from MSB to LSB: MSB goes to index 0
        const int bitPos = rbits - (i + 1) * lbits;
        const int actualBitPos = (bitPos < 0) ? 0 : bitPos;
        const int actualWidth = (bitPos < 0) ? (lbits + bitPos) : lbits;
        q.atWrite(i) = VL_SEL_IWII_TTTT(rbits, rwp, actualBitPos, actualWidth) & mask;
    }
}

static inline void VL_UNPACK_RI_W(int lbits, int rbits, VlQueue<IData>& q, WDataInP rwp) {
    const int size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < size; ++i) {
        // Extract from MSB to LSB: MSB goes to index 0
        const int bitPos = rbits - (i + 1) * lbits;
        const int actualBitPos = (bitPos < 0) ? 0 : bitPos;
        const int actualWidth = (bitPos < 0) ? (lbits + bitPos) : lbits;
        q.atWrite(i) = VL_SEL_IWII_TTTT(rbits, rwp, actualBitPos, actualWidth) & mask;
    }
}

static inline void VL_UNPACK_RQ_W(int lbits, int rbits, VlQueue<QData>& q, WDataInP rwp) {
    const int size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    const QData mask = VL_MASK_Q(lbits);
    for (size_t i = 0; i < size; ++i) {
        // Extract from MSB to LSB: MSB goes to index 0
        const int bitPos = rbits - (i + 1) * lbits;
        const int actualBitPos = (bitPos < 0) ? 0 : bitPos;
        const int actualWidth = (bitPos < 0) ? (lbits + bitPos) : lbits;
        q.atWrite(i) = VL_SEL_QWII_TTTT(rbits, rwp, actualBitPos, actualWidth) & mask;
    }
}

template <std::size_t N_Words>
static inline void VL_UNPACK_RW_W(int lbits, int rbits, VlQueue<VlWide<N_Words>>& q,
                                  WDataInP rwp) {
    const int size = (rbits + lbits - 1) / lbits;
    q.renew(size);
    for (size_t i = 0; i < size; ++i) {
        // Extract from MSB to LSB: MSB goes to index 0
        const int bitPos = rbits - (i + 1) * lbits;
        const int actualBitPos = (bitPos < 0) ? 0 : bitPos;
        const int actualWidth = (bitPos < 0) ? (lbits + bitPos) : lbits;
        VL_SEL_WWII_TTTT(actualWidth, rbits, q.atWrite(i), rwp, actualBitPos, actualWidth);
    }
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_I(int lbits, int /*rbits*/, VlUnpacked<CData, N_Depth>& q,
                                  IData from) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_I(int lbits, int /*rbits*/, VlUnpacked<SData, N_Depth>& q,
                                  IData from) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_I(int lbits, int /*rbits*/, VlUnpacked<IData, N_Depth>& q,
                                  IData from) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <typename T_Sub, std::size_t N_Sub, std::size_t N_Depth>
static inline void VL_UNPACK_UI_I(const int lbits, const int rbits,
                                  VlUnpacked<VlUnpacked<T_Sub, N_Sub>, N_Depth>& q,
                                  const IData from) {
    const int sub_bits = VlUnpackedElements<VlUnpacked<T_Sub, N_Sub>>::count * lbits;
    for (size_t i = 0; i < N_Depth; ++i) {
        const IData sub_from = (from >> ((N_Depth - 1 - i) * sub_bits));
        VL_UNPACK_UI_I(lbits, sub_bits, q[i], sub_from);
    }
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_Q(int lbits, int /*rbits*/, VlUnpacked<CData, N_Depth>& q,
                                  QData from) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_Q(int lbits, int /*rbits*/, VlUnpacked<SData, N_Depth>& q,
                                  QData from) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_Q(int lbits, int /*rbits*/, VlUnpacked<IData, N_Depth>& q,
                                  QData from) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <typename T_Sub, std::size_t N_Sub, std::size_t N_Depth>
static inline void VL_UNPACK_UI_Q(const int lbits, const int rbits,
                                  VlUnpacked<VlUnpacked<T_Sub, N_Sub>, N_Depth>& q,
                                  const QData from) {
    const int sub_bits = VlUnpackedElements<VlUnpacked<T_Sub, N_Sub>>::count * lbits;
    for (size_t i = 0; i < N_Depth; ++i) {
        const QData sub_from = (from >> ((N_Depth - 1 - i) * sub_bits));
        VL_UNPACK_UI_Q(lbits, sub_bits, q[i], sub_from);
    }
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UQ_Q(int lbits, int /*rbits*/, VlUnpacked<QData, N_Depth>& q,
                                  QData from) {
    const QData mask = VL_MASK_Q(lbits);
    for (size_t i = 0; i < N_Depth; ++i) q[i] = (from >> ((N_Depth - 1 - i) * lbits)) & mask;
}

template <typename T_Sub, std::size_t N_Sub, std::size_t N_Depth>
static inline void VL_UNPACK_UI_W(const int lbits, const int rbits,
                                  VlUnpacked<VlUnpacked<T_Sub, N_Sub>, N_Depth>& q, WDataInP rwp,
                                  const int bit_offset = 0) {
    const int sub_bits = VlUnpackedElements<VlUnpacked<T_Sub, N_Sub>>::count * lbits;
    for (size_t i = 0; i < N_Depth; ++i) {
        VL_UNPACK_UI_W(lbits, rbits, q[i], rwp, bit_offset + (N_Depth - 1 - i) * sub_bits);
    }
}

template <typename T_Sub, std::size_t N_Sub, std::size_t N_Depth>
static inline void VL_UNPACK_UQ_W(const int lbits, const int rbits,
                                  VlUnpacked<VlUnpacked<T_Sub, N_Sub>, N_Depth>& q, WDataInP rwp,
                                  const int bit_offset = 0) {
    const int sub_bits = VlUnpackedElements<VlUnpacked<T_Sub, N_Sub>>::count * lbits;
    for (size_t i = 0; i < N_Depth; ++i) {
        VL_UNPACK_UQ_W(lbits, rbits, q[i], rwp, bit_offset + (N_Depth - 1 - i) * sub_bits);
    }
}

template <typename T_Sub, std::size_t N_Sub, std::size_t N_Depth>
static inline void VL_UNPACK_UW_W(const int lbits, const int rbits,
                                  VlUnpacked<VlUnpacked<T_Sub, N_Sub>, N_Depth>& q, WDataInP rwp,
                                  const int bit_offset = 0) {
    const int sub_bits = VlUnpackedElements<VlUnpacked<T_Sub, N_Sub>>::count * lbits;
    for (size_t i = 0; i < N_Depth; ++i) {
        VL_UNPACK_UW_W(lbits, rbits, q[i], rwp, bit_offset + (N_Depth - 1 - i) * sub_bits);
    }
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_W(int lbits, int rbits, VlUnpacked<CData, N_Depth>& q,
                                  WDataInP rwp, const int bit_offset = 0) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i)
        q[i] = VL_SEL_IWII_TTTT(rbits, rwp, bit_offset + (N_Depth - 1 - i) * lbits, lbits) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_W(int lbits, int rbits, VlUnpacked<SData, N_Depth>& q,
                                  WDataInP rwp, const int bit_offset = 0) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i)
        q[i] = VL_SEL_IWII_TTTT(rbits, rwp, bit_offset + (N_Depth - 1 - i) * lbits, lbits) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UI_W(int lbits, int rbits, VlUnpacked<IData, N_Depth>& q,
                                  WDataInP rwp, const int bit_offset = 0) {
    const IData mask = VL_MASK_I(lbits);
    for (size_t i = 0; i < N_Depth; ++i)
        q[i] = VL_SEL_IWII_TTTT(rbits, rwp, bit_offset + (N_Depth - 1 - i) * lbits, lbits) & mask;
}

template <std::size_t N_Depth>
static inline void VL_UNPACK_UQ_W(int lbits, int rbits, VlUnpacked<QData, N_Depth>& q,
                                  WDataInP rwp, const int bit_offset = 0) {
    const QData mask = VL_MASK_Q(lbits);
    for (size_t i = 0; i < N_Depth; ++i)
        q[i] = VL_SEL_QWII_TTTT(rbits, rwp, bit_offset + (N_Depth - 1 - i) * lbits, lbits) & mask;
}

template <std::size_t N_Depth, std::size_t N_Words>
static inline void VL_UNPACK_UW_W(int lbits, int rbits, VlUnpacked<VlWide<N_Words>, N_Depth>& q,
                                  WDataInP rwp, const int bit_offset = 0) {
    for (size_t i = 0; i < N_Depth; ++i)
        VL_SEL_WWII_TTTT(lbits, rbits, q[i], rwp, bit_offset + (N_Depth - 1 - i) * lbits, lbits);
}

// Return QData from double (numeric)
// EMIT_RULE: VL_RTOIROUND_Q_D:  oclean=dirty; lclean==clean/real
static inline QData VL_RTOIROUND_Q_D(double lhs) VL_PURE {
    // IEEE format: [63]=sign [62:52]=exp+1023 [51:0]=mantissa
    // This does not need to support subnormals as they are sub-integral
    lhs = VL_ROUND(lhs);
    if (lhs == 0.0) return 0;
    const QData q = VL_CVT_Q_D(lhs);
    const int lsb = static_cast<int>((q >> 52ULL) & VL_MASK_Q(11)) - 1023 - 52;
    const uint64_t mantissa = (q & VL_MASK_Q(52)) | (1ULL << 52);
    uint64_t out = 0;
    if (lsb < 0) {
        out = mantissa >> -lsb;
    } else if (lsb < 64) {
        out = mantissa << lsb;
    }
    if (lhs < 0) out = -out;
    return out;
}
static inline IData VL_RTOIROUND_I_D(double lhs) VL_PURE {
    return static_cast<IData>(VL_RTOIROUND_Q_D(lhs));
}
static inline WDataOutP VL_RTOIROUND_W_D(int obits, WDataOutP owp, double lhs) VL_MT_SAFE {
    // IEEE format: [63]=sign [62:52]=exp+1023 [51:0]=mantissa
    // This does not need to support subnormals as they are sub-integral
    lhs = VL_ROUND(lhs);
    VL_ZERO_W_T(obits, owp);
    if (lhs == 0.0) return owp;
    const QData q = VL_CVT_Q_D(lhs);
    const int lsb = static_cast<int>((q >> 52ULL) & VL_MASK_Q(11)) - 1023 - 52;
    const uint64_t mantissa = (q & VL_MASK_Q(52)) | (1ULL << 52);
    if (lsb < 0) {
        VL_SET_WQ_T(owp, mantissa >> -lsb);
    } else if (lsb < obits) {
        _vl_insert_WQ_T(owp, mantissa, lsb + 52, lsb);
    }
    if (lhs < 0) VL_NEGATE_INPLACE_W_T(VL_WORDS_I(obits), owp);
    return owp;
}

//======================================================================
// Range assignments

// EMIT_RULE: VL_ASSIGNRANGE:  rclean=dirty;
static inline void VL_ASSIGNSEL_II_TT(int rbits, int obits, int lsb, CData& lhsr,
                                      IData rhs) VL_PURE {
    _vl_insert_II(lhsr, rhs, lsb + obits - 1, lsb, rbits);
}
static inline void VL_ASSIGNSEL_II_TT(int rbits, int obits, int lsb, SData& lhsr,
                                      IData rhs) VL_PURE {
    _vl_insert_II(lhsr, rhs, lsb + obits - 1, lsb, rbits);
}
static inline void VL_ASSIGNSEL_II_TT(int rbits, int obits, int lsb, IData& lhsr,
                                      IData rhs) VL_PURE {
    _vl_insert_II(lhsr, rhs, lsb + obits - 1, lsb, rbits);
}
static inline void VL_ASSIGNSEL_QI_TT(int rbits, int obits, int lsb, QData& lhsr,
                                      IData rhs) VL_PURE {
    _vl_insert_QQ(lhsr, rhs, lsb + obits - 1, lsb, rbits);
}
static inline void VL_ASSIGNSEL_QQ_TT(int rbits, int obits, int lsb, QData& lhsr,
                                      QData rhs) VL_PURE {
    _vl_insert_QQ(lhsr, rhs, lsb + obits - 1, lsb, rbits);
}
// static inline void VL_ASSIGNSEL_IIIW(int obits, int lsb, IData& lhsr, WDataInP const rwp)
// VL_MT_SAFE { Illegal, as lhs width >= rhs width

// clang-format off
#define VL_ASSIGNSEL_WI_GEN(lhsSuffix) \
static inline void VL_ASSIGNSEL_WI_##lhsSuffix##T(int rbits, int obits, int lsb, WDataOutP iowp, IData rhs) \
        VL_MT_SAFE { \
        _vl_insert_WI_##lhsSuffix(iowp, rhs, lsb + obits - 1, lsb, rbits); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_ASSIGNSEL_WI_GEN)
#undef VL_ASSIGNSEL_WI_GEN

// clang-format off
#define VL_ASSIGNSEL_WQ_GEN(lhsSuffix) \
static inline void VL_ASSIGNSEL_WQ_##lhsSuffix##T(int rbits, int obits, int lsb, \
                                                      WDataOutP iowp, QData rhs) VL_MT_SAFE { \
        _vl_insert_WQ_##lhsSuffix(iowp, rhs, lsb + obits - 1, lsb, rbits); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_ASSIGNSEL_WQ_GEN)
#undef VL_ASSIGNSEL_WQ_GEN

// clang-format off
#define VL_ASSIGNSEL_WW_GEN(lhsSuffix, rhsSuffix) \
static inline void VL_ASSIGNSEL_WW_##lhsSuffix##rhsSuffix( \
        int rbits, int obits, int lsb, WDataOutP iowp, WDataInP const rwp) VL_MT_SAFE { \
        _vl_insert_WW_##lhsSuffix##rhsSuffix(iowp, rwp, lsb + obits - 1, lsb, rbits); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_ASSIGNSEL_WW_GEN)
#undef VL_ASSIGNSEL_WI_GEN

//====================================================
// Range assignments

// These additional functions copy bits range [obis+roffset-1:roffset] from rhs to lower bits
// of lhs(select before assigning). Rhs should always be wider than lhs.
static inline void VL_SELASSIGN_II_TT(int rbits, int obits, CData& lhsr, IData rhs,
                                      int roffset) VL_PURE {
    _vl_insert_II(lhsr, rhs >> roffset, obits - 1, 0, rbits);
}
static inline void VL_SELASSIGN_II_TT(int rbits, int obits, SData& lhsr, IData rhs,
                                      int roffset) VL_PURE {
    _vl_insert_II(lhsr, rhs >> roffset, obits - 1, 0, rbits);
}
static inline void VL_SELASSIGN_II_TT(int rbits, int obits, IData& lhsr, IData rhs,
                                      int roffset) VL_PURE {
    _vl_insert_II(lhsr, rhs >> roffset, obits - 1, 0, rbits);
}
static inline void VL_SELASSIGN_IQ_TT(int rbits, int obits, CData& lhsr, QData rhs,
                                      int roffset) VL_PURE {
    // it will be truncated to right CData mask
    const CData cleanmask = VL_MASK_I(rbits);
    const CData insmask = VL_MASK_I(obits);
    lhsr = (lhsr & ~insmask) | (static_cast<CData>(rhs >> roffset) & (insmask & cleanmask));
}
static inline void VL_SELASSIGN_IQ_TT(int rbits, int obits, SData& lhsr, QData rhs,
                                      int roffset) VL_PURE {
    // it will be truncated to right CData mask
    const SData cleanmask = VL_MASK_I(rbits);
    const SData insmask = VL_MASK_I(obits);
    lhsr = (lhsr & ~insmask) | (static_cast<SData>(rhs >> roffset) & (insmask & cleanmask));
}
static inline void VL_SELASSIGN_IQ_TT(int rbits, int obits, IData& lhsr, QData rhs,
                                      int roffset) VL_PURE {
    const IData cleanmask = VL_MASK_I(rbits);
    const IData insmask = VL_MASK_I(obits);
    lhsr = (lhsr & ~insmask) | (static_cast<IData>(rhs >> roffset) & (insmask & cleanmask));
}

static inline void VL_SELASSIGN_QQ_TT(int rbits, int obits, QData& lhsr, QData rhs,
                                      int roffset) VL_PURE {
    _vl_insert_QQ(lhsr, rhs >> roffset, obits - 1, 0, rbits);
}

// clang-format off
#define VL_SELASSIGN_IW_GEN(rhsSuffix) \
static inline void VL_SELASSIGN_IW_T##rhsSuffix(int rbits, int obits, CData& lhsr, \
                                                    WDataInP const rhs, int roffset) VL_MT_SAFE { \
        IData l = static_cast<IData>(lhsr); \
        _vl_insert_IW_T##rhsSuffix(l, rhs, roffset + obits - 1, roffset, rbits); \
        lhsr = static_cast<CData>(l); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SELASSIGN_IW_GEN)
#undef VL_SELASSIGN_IW_GEN

// clang-format off
#define VL_SELASSIGN_IW_GEN(rhsSuffix) \
static inline void VL_SELASSIGN_IW_T##rhsSuffix(int rbits, int obits, SData& lhsr, \
                                                    WDataInP const rhs, int roffset) VL_MT_SAFE { \
        IData l = static_cast<IData>(lhsr); \
        _vl_insert_IW_T##rhsSuffix(l, rhs, roffset + obits - 1, roffset, rbits); \
        lhsr = static_cast<SData>(l); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SELASSIGN_IW_GEN)
#undef VL_SELASSIGN_IW_GEN

// clang-format off
#define VL_SELASSIGN_IW_GEN(rhsSuffix) \
static inline void VL_SELASSIGN_IW_T##rhsSuffix(int rbits, int obits, IData& lhsr, \
                                                    WDataInP const rhs, int roffset) VL_MT_SAFE { \
        _vl_insert_IW_T##rhsSuffix(lhsr, rhs, roffset + obits - 1, roffset, rbits); \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SELASSIGN_IW_GEN)
#undef VL_SELASSIGN_IW_GEN

// clang-format off
#define VL_SELASSIGN_QW_GEN(rhsSuffix) \
static inline void VL_SELASSIGN_QW_T##rhsSuffix(int rbits, int obits, QData& lhsr, \
                                                    WDataInP const rhs, int roffset) VL_MT_SAFE { \
        /* assert VL_QDATASIZE >= rbits > VL_IDATASIZE; */ \
        IData low = static_cast<IData>(lhsr); \
        IData high = static_cast<IData>(lhsr >> VL_IDATASIZE); \
        if (obits <= VL_IDATASIZE) { \
            _vl_insert_IW_T##rhsSuffix(low, rhs, obits + roffset - 1, roffset, VL_IDATASIZE); \
        } else { \
            _vl_insert_IW_T##rhsSuffix(low, rhs, roffset + VL_IDATASIZE - 1, roffset, \
                                       VL_IDATASIZE); \
            _vl_insert_IW_T##rhsSuffix(high, rhs, roffset + obits - 1, roffset + VL_IDATASIZE, \
                                       rbits - VL_IDATASIZE); \
        } \
        lhsr = (static_cast<QData>(high) << VL_IDATASIZE) | low; \
    }
// clang-format on
VL_GEN_HELPER_ONE_ARG(VL_SELASSIGN_QW_GEN)
#undef VL_SELASSIGN_QW_GEN

// clang-format off
#define VL_SELASSIGN_WW_GEN(lhsSuffix, rhsSuffix) \
static inline void VL_SELASSIGN_WW_##lhsSuffix##rhsSuffix( \
        int rbits, int obits, WDataOutP iowp, WDataInP rwp, int roffset) VL_MT_SAFE { \
        /* assert rbits > VL_QDATASIZE */ \
        const int wordoff = roffset / VL_EDATASIZE; \
        const int lsb = roffset & VL_SIZEBITS_E; \
        const int upperbits = lsb == 0 ? 0 : VL_EDATASIZE - lsb; \
        /* If roffset is not aligned, we copy some bits to align it. */ \
        if (lsb != 0) { \
            const int w = obits < upperbits ? obits : upperbits; \
            const int insmask = VL_MASK_E(w); \
            const WDataOutP iowp0 = VL_GET_ELEM(lhsSuffix, iowp, 0); \
            *iowp0 = (*iowp0 & ~insmask) \
                     | ((*VL_GET_ELEM(rhsSuffix, rwp, wordoff) >> lsb) & insmask); \
            /* cppcheck-suppress knownConditionTrueFalse */ \
            if (w == obits) return; \
            obits -= w; \
        } \
        rwp = VL_GET_ELEM(rhsSuffix, rwp, wordoff + (lsb != 0)) - VL_GET_TYPE_OFFSET(rhsSuffix); \
        /* ^ the '- VL_GET_TYPE_OFFSET(rhsSuffix)' is here to pretend that this is not a middle \
         * of some wide - we need this since _vl_insert_WW_** will add offset */ \
        _vl_insert_WW_##lhsSuffix##rhsSuffix(iowp, rwp, upperbits + obits - 1, upperbits, rbits); \
    }
// clang-format on
VL_GEN_HELPER_TWO_ARG(VL_SELASSIGN_WW_GEN)
#undef VL_SELASSIGN_WW_GEN

//======================================================================
// Triops

// This must be a macro in order for short-circuiting of the values to work.
#define VL_COND_WIWW_TTTT(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_TT(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_TTVV(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_TV(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_TTXX(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_TX(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_VTTT(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_VT(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_VTVV(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_VV(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_VTXX(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_VX(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_XTTT(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_XT(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_XTVV(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_XV(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_XTXX(obits, owp, cond, w1p, w2p) \
    VL_ASSIGN_W_XX(obits, owp, (cond) ? (w1p) : (w2p))
#define VL_COND_WIWW_TTTV(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_TT(obits, owp, w1p) : VL_ASSIGN_W_TV(obits, owp, w2p))
#define VL_COND_WIWW_TTTX(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_TT(obits, owp, w1p) : VL_ASSIGN_W_TX(obits, owp, w2p))
#define VL_COND_WIWW_TTVT(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_TV(obits, owp, w1p) : VL_ASSIGN_W_TT(obits, owp, w2p))
#define VL_COND_WIWW_TTVX(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_TV(obits, owp, w1p) : VL_ASSIGN_W_TX(obits, owp, w2p))
#define VL_COND_WIWW_TTXT(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_TX(obits, owp, w1p) : VL_ASSIGN_W_TT(obits, owp, w2p))
#define VL_COND_WIWW_TTXV(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_TX(obits, owp, w1p) : VL_ASSIGN_W_TV(obits, owp, w2p))
#define VL_COND_WIWW_VTTV(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_VT(obits, owp, w1p) : VL_ASSIGN_W_VV(obits, owp, w2p))
#define VL_COND_WIWW_VTTX(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_VT(obits, owp, w1p) : VL_ASSIGN_W_VX(obits, owp, w2p))
#define VL_COND_WIWW_VTVT(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_VV(obits, owp, w1p) : VL_ASSIGN_W_VT(obits, owp, w2p))
#define VL_COND_WIWW_VTVX(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_VV(obits, owp, w1p) : VL_ASSIGN_W_VX(obits, owp, w2p))
#define VL_COND_WIWW_VTXT(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_VX(obits, owp, w1p) : VL_ASSIGN_W_VT(obits, owp, w2p))
#define VL_COND_WIWW_VTXV(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_VX(obits, owp, w1p) : VL_ASSIGN_W_VV(obits, owp, w2p))
#define VL_COND_WIWW_XTTV(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_XT(obits, owp, w1p) : VL_ASSIGN_W_XV(obits, owp, w2p))
#define VL_COND_WIWW_XTTX(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_XT(obits, owp, w1p) : VL_ASSIGN_W_XX(obits, owp, w2p))
#define VL_COND_WIWW_XTVT(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_XV(obits, owp, w1p) : VL_ASSIGN_W_XT(obits, owp, w2p))
#define VL_COND_WIWW_XTVX(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_XV(obits, owp, w1p) : VL_ASSIGN_W_XX(obits, owp, w2p))
#define VL_COND_WIWW_XTXT(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_XX(obits, owp, w1p) : VL_ASSIGN_W_XT(obits, owp, w2p))
#define VL_COND_WIWW_XTXV(obits, owp, cond, w1p, w2p) \
    ((cond) ? VL_ASSIGN_W_XX(obits, owp, w1p) : VL_ASSIGN_W_XV(obits, owp, w2p))

//======================================================================
// Constification

// VL_CONST_W_#T/V/X(int obits, WDataOutP owp, {IData data0, .... IData data(#-1)})
// Sets wide vector words to specified constant words.
// These macros are used when o might represent more words then are given as constants,
// hence all upper words must be zeroed.

#define VL_C_END_(obits, wordsSet) \
    VL_MEMSET_ZERO_W(o + (wordsSet), VL_WORDS_I(obits) - (wordsSet)); \
    return o

static inline WDataOutP VL_CONST_W_T(const int obits, WDataOutP const o,
                                     std::initializer_list<EData> values) VL_MT_SAFE {
    VL_MEMCPY_W(o, WDataInP::external(values.begin()), values.size());
    VL_C_END_(obits, values.size());
}

// clang-format off
#define VL_CONST_W_GEN(outputSuffix) \
static inline WDataOutP VL_CONST_W_##outputSuffix( \
        const int obits, WDataOutP o, std::initializer_list<EData> values) VL_MT_SAFE { \
        const WDataOutP resultp = o; \
        o += VL_GET_TYPE_OFFSET(outputSuffix); \
        for (EData v : values) { \
            *o = v; \
            o += VL_GET_TYPE_JUMP(outputSuffix); \
        } \
        VL_ZERO_OFFSET_W_##outputSuffix(obits - (values.size() * VL_EDATASIZE), o); \
        return resultp; \
    }
// clang-format on
VL_CONST_W_GEN(V)
VL_CONST_W_GEN(X)
#undef VL_CONST_W_GEN

//======================================================================
// Strings

extern std::string VL_PUTC_N(const std::string& lhs, IData rhs, CData ths) VL_PURE;
extern CData VL_GETC_N(const std::string& lhs, IData rhs) VL_PURE;
extern std::string VL_SUBSTR_N(const std::string& lhs, IData rhs, IData ths) VL_PURE;

inline IData VL_CMP_NN(const std::string& lhs, const std::string& rhs, bool ignoreCase) VL_PURE {
    // SystemVerilog does not allow a string variable to contain '\0'.
    // So C functions such as strcmp() can correctly compare strings.
    if (ignoreCase) { return VL_STRCASECMP(lhs.c_str(), rhs.c_str()); }
    return std::strcmp(lhs.c_str(), rhs.c_str());
}

extern IData VL_ATOI_N(const std::string& str, int base) VL_PURE;
extern IData VL_NTOI_I(int obits, const std::string& str) VL_PURE;
extern QData VL_NTOI_Q(int obits, const std::string& str) VL_PURE;
extern void VL_NTOI_W(int obits, WDataOutP owp, const std::string& str,
                      int truncFront = 0) VL_PURE;

extern IData VL_FGETS_NI(std::string& dest, IData fpi) VL_MT_SAFE;

//======================================================================
// Dist functions

extern IData VL_DIST_CHI_SQUARE(IData& seedr, IData udeg_of_free) VL_MT_SAFE;
extern IData VL_DIST_ERLANG(IData& seedr, IData uk, IData umean) VL_MT_SAFE;
extern IData VL_DIST_EXPONENTIAL(IData& seedr, IData umean) VL_MT_SAFE;
extern IData VL_DIST_NORMAL(IData& seedr, IData umean, IData udeviation) VL_MT_SAFE;
extern IData VL_DIST_POISSON(IData& seedr, IData umean) VL_MT_SAFE;
extern IData VL_DIST_T(IData& seedr, IData udeg_of_free) VL_MT_SAFE;
extern IData VL_DIST_UNIFORM(IData& seedr, IData ustart, IData uend) VL_MT_SAFE;

//======================================================================
// Conversion functions

extern std::string VL_CVT_PACK_STR_NW(int lwords, const WDataInP lwp) VL_PURE;
extern std::string VL_CVT_PACK_STR_ND(const VlQueue<std::string>& q) VL_PURE;
inline std::string VL_CVT_PACK_STR_NQ(QData lhs) VL_PURE {
    VlWide<VL_WQ_WORDS_E> lw;
    VL_SET_WQ_T(lw, lhs);
    return VL_CVT_PACK_STR_NW(VL_WQ_WORDS_E, lw);
}
inline std::string VL_CVT_PACK_STR_NN(const std::string& lhs) VL_PURE { return lhs; }
inline std::string& VL_CVT_PACK_STR_NN(std::string& lhs) VL_PURE { return lhs; }
inline std::string VL_CVT_PACK_STR_NI(IData lhs) VL_PURE {
    VlWide<VL_WQ_WORDS_E> lw;
    VL_SET_WI(lw, lhs);
    return VL_CVT_PACK_STR_NW(1, lw);
}
inline std::string VL_CONCATN_NNN(const std::string& lhs, const std::string& rhs) VL_PURE {
    return lhs + rhs;
}
inline std::string VL_REPLICATEN_NNQ(const std::string& lhs, IData rep) VL_PURE {
    std::string result;
    result.reserve(lhs.length() * rep);
    for (unsigned times = 0; times < rep; ++times) result += lhs;
    return result;
}
inline std::string VL_REPLICATEN_NNI(const std::string& lhs, IData rep) VL_PURE {
    return VL_REPLICATEN_NNQ(lhs, rep);
}

inline IData VL_LEN_IN(const std::string& ld) { return static_cast<IData>(ld.length()); }
extern std::string VL_TOLOWER_NN(const std::string& ld) VL_PURE;
extern std::string VL_TOUPPER_NN(const std::string& ld) VL_PURE;

extern IData VL_FERROR_IN(IData fpi, std::string& outputr) VL_MT_SAFE;
extern IData VL_FERROR_IW(IData fpi, int obits, WDataOutP outwp) VL_MT_SAFE;
extern IData VL_FOPEN_NN(const std::string& filename, const std::string& mode) VL_MT_SAFE;
extern IData VL_FOPEN_MCD_N(const std::string& filename) VL_MT_SAFE;
extern void VL_READMEM_N(bool hex, int bits, QData depth, int array_lsb,
                         const std::string& filename, void* memp, QData start,
                         QData end) VL_MT_SAFE;
extern void VL_WRITEMEM_N(bool hex, int bits, QData depth, int array_lsb,
                          const std::string& filename, const void* memp, QData start,
                          QData end) VL_MT_SAFE;
extern IData VL_SSCANF_INNX(int lbits, const std::string& ld, const std::string& format, int argc,
                            ...) VL_MT_SAFE;
extern void VL_TIMEFORMAT_IINI(bool hasUnits, int units, bool hasPrecision, int precision,
                               bool hasSuffix, const std::string& suffix, bool hasWidth, int width,
                               VerilatedContext* contextp) VL_MT_SAFE;
extern IData VL_VALUEPLUSARGS_INW(int rbits, const std::string& ld, WDataOutP rwp) VL_MT_SAFE;
inline IData VL_VALUEPLUSARGS_IND(int rbits, const std::string& ld, double& rdr) VL_MT_SAFE {
    VlWide<2> rwp;
    const IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = VL_CVT_D_Q(VL_SET_QW(rwp));
    return got;
}
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, CData& rdr) VL_MT_SAFE {
    VlWide<2> rwp;
    const IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, SData& rdr) VL_MT_SAFE {
    VlWide<2> rwp;
    const IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, IData& rdr) VL_MT_SAFE {
    VlWide<2> rwp;
    const IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INQ(int rbits, const std::string& ld, QData& rdr) VL_MT_SAFE {
    VlWide<2> rwp;
    const IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = VL_SET_QW(rwp);
    return got;
}
inline IData VL_VALUEPLUSARGS_INQ(int rbits, const std::string& ld, double& rdr) VL_MT_SAFE {
    VlWide<2> rwp;
    const IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = VL_CVT_D_Q(VL_SET_QW(rwp));
    return got;
}
extern IData VL_VALUEPLUSARGS_INN(int, const std::string& ld, std::string& rdr) VL_MT_SAFE;

uint64_t VL_MURMUR64_HASH(const char* key) VL_PURE;

//======================================================================

#undef VL_GEN_HELPER_THREE_ARG
#undef VL_GEN_HELPER_TWO_ARG
#undef VL_GEN_HELPER_ONE_ARG

#endif  // Guard
