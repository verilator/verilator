// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilator: Linked against all applications using Verilated source.
///
///     This file must be compiled and linked against all objects
///     created from Verilator.
///
/// Code available from: https://verilator.org
///
//=========================================================================

#define _VERILATED_CPP_

#include "verilatedos.h"
#include "verilated_imp.h"

#include "verilated_config.h"

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <sstream>
#include <sys/stat.h>  // mkdir
#include <list>
#include <limits>
#include <utility>

// clang-format off
#if defined(_WIN32) || defined(__MINGW32__)
# include <direct.h>  // mkdir
#endif
// clang-format on

/// Max static char array for VL_VALUE_STRING
constexpr unsigned VL_VALUE_STRING_MAX_WIDTH = 8192;

//===========================================================================
// Static sanity checks

static_assert(sizeof(vluint8_t) == 1, "vluint8_t is missized");
static_assert(sizeof(vluint16_t) == 2, "vluint8_t is missized");
static_assert(sizeof(vluint32_t) == 4, "vluint8_t is missized");
static_assert(sizeof(vluint64_t) == 8, "vluint8_t is missized");

//===========================================================================
// Global variables

// Slow path variables
VerilatedMutex Verilated::s_mutex;

// Keep below together in one cache line
Verilated::Serialized Verilated::s_s;
Verilated::NonSerialized Verilated::s_ns;
VL_THREAD_LOCAL Verilated::ThreadLocal Verilated::t_s;

Verilated::CommandArgValues Verilated::s_args;

VerilatedImp::VerilatedImpU VerilatedImp::s_s;

// Guarantees to call setup() and teardown() just once.
struct VerilatedInitializer {
    VerilatedInitializer() { setup(); }
    ~VerilatedInitializer() { teardown(); }
    void setup() {
        static bool done = false;
        if (!done) {
            VerilatedImp::setup();
            Verilated::s_ns.setup();
            done = true;
        }
    }
    void teardown() {
        static bool done = false;
        if (!done) {
            VerilatedImp::teardown();
            Verilated::s_ns.teardown();
            done = true;
        }
    }
} s_VerilatedInitializer;

//===========================================================================
// User definable functions
// Note a TODO is a future version of the API will pass a structure so that
// the calling arguments allow for extension

#ifndef VL_USER_FINISH  ///< Define this to override this function
void vl_finish(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    if (false && hier) {}
    VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
        "- %s:%d: Verilog $finish\n", filename, linenum);
    if (Verilated::gotFinish()) {
        VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
            "- %s:%d: Second verilog $finish, exiting\n", filename, linenum);
        Verilated::runFlushCallbacks();
        Verilated::runExitCallbacks();
        exit(0);
    }
    Verilated::gotFinish(true);
}
#endif

#ifndef VL_USER_STOP  ///< Define this to override this function
void vl_stop(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    Verilated::gotFinish(true);
    Verilated::runFlushCallbacks();
    vl_fatal(filename, linenum, hier, "Verilog $stop");
}
#endif

#ifndef VL_USER_FATAL  ///< Define this to override this function
void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_UNSAFE {
    if (false && hier) {}
    Verilated::gotFinish(true);
    if (filename && filename[0]) {
        // Not VL_PRINTF_MT, already on main thread
        VL_PRINTF("%%Error: %s:%d: %s\n", filename, linenum, msg);
    } else {
        VL_PRINTF("%%Error: %s\n", msg);
    }
    Verilated::runFlushCallbacks();

    VL_PRINTF("Aborting...\n");  // Not VL_PRINTF_MT, already on main thread

    // Second flush in case VL_PRINTF does something needing a flush
    Verilated::runFlushCallbacks();

    // Callbacks prior to termination
    Verilated::runExitCallbacks();
    abort();
}
#endif

#ifndef VL_USER_STOP_MAYBE  ///< Define this to override this function
void vl_stop_maybe(const char* filename, int linenum, const char* hier, bool maybe) VL_MT_UNSAFE {
    Verilated::errorCountInc();
    if (maybe && Verilated::errorCount() < Verilated::errorLimit()) {
        VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
            "-Info: %s:%d: %s\n", filename, linenum,
            "Verilog $stop, ignored due to +verilator+error+limit");
    } else {
        vl_stop(filename, linenum, hier);
    }
}
#endif

//===========================================================================
// Wrapper to call certain functions via messages when multithreaded

void VL_FINISH_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg([=]() {  //
        vl_finish(filename, linenum, hier);
    }));
#else
    vl_finish(filename, linenum, hier);
#endif
}

void VL_STOP_MT(const char* filename, int linenum, const char* hier, bool maybe) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg([=]() {  //
        vl_stop_maybe(filename, linenum, hier, maybe);
    }));
#else
    vl_stop_maybe(filename, linenum, hier, maybe);
#endif
}

void VL_FATAL_MT(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg([=]() {  //
        vl_fatal(filename, linenum, hier, msg);
    }));
#else
    vl_fatal(filename, linenum, hier, msg);
#endif
}

//===========================================================================
// Debug prints

/// sprintf but return as string (this isn't fast, for print messages only)
std::string _vl_string_vprintf(const char* formatp, va_list ap) VL_MT_SAFE {
    va_list aq;
    va_copy(aq, ap);
    int len = VL_VSNPRINTF(nullptr, 0, formatp, aq);
    va_end(aq);
    if (VL_UNLIKELY(len < 1)) return "";

    char* bufp = new char[len + 1];
    VL_VSNPRINTF(bufp, len + 1, formatp, ap);

    std::string out = std::string(bufp, len);
    delete[] bufp;
    return out;
}

vluint64_t _vl_dbg_sequence_number() VL_MT_SAFE {
#ifdef VL_THREADED
    static std::atomic<vluint64_t> sequence;
#else
    static vluint64_t sequence = 0;
#endif
    return ++sequence;
}

vluint32_t VL_THREAD_ID() VL_MT_SAFE {
#ifdef VL_THREADED
    // Alternative is to use std::this_thread::get_id, but that returns a
    // hard-to-read number and is very slow
    static std::atomic<vluint32_t> s_nextId(0);
    static VL_THREAD_LOCAL vluint32_t t_myId = ++s_nextId;
    return t_myId;
#else
    return 0;
#endif
}

void VL_DBG_MSGF(const char* formatp, ...) VL_MT_SAFE {
    // We're still using c printf formats instead of operator<< so we can avoid the heavy
    // includes that otherwise would be required in every Verilated module
    va_list ap;
    va_start(ap, formatp);
    std::string out = _vl_string_vprintf(formatp, ap);
    va_end(ap);
    // printf("-imm-V{t%d,%" VL_PRI64 "d}%s", VL_THREAD_ID(), _vl_dbg_sequence_number(),
    // out.c_str());

    // Using VL_PRINTF not VL_PRINTF_MT so that we can call VL_DBG_MSGF
    // from within the guts of the thread execution machinery (and it goes
    // to the screen and not into the queues we're debugging)
    VL_PRINTF("-V{t%u,%" VL_PRI64 "u}%s", VL_THREAD_ID(), _vl_dbg_sequence_number(), out.c_str());
}

#ifdef VL_THREADED
void VL_PRINTF_MT(const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    std::string out = _vl_string_vprintf(formatp, ap);
    va_end(ap);
    VerilatedThreadMsgQueue::post(VerilatedMsg([=]() {  //
        VL_PRINTF("%s", out.c_str());
    }));
}
#endif

//===========================================================================
// Overall class init

Verilated::Serialized::Serialized() {
    s_calcUnusedSigs = false;
    s_gotFinish = false;
    s_assertOn = true;
    s_fatalOnVpiError = true;  // retains old default behaviour
    s_errorCount = 0;
    s_errorLimit = 1;
    s_randReset = 0;
    s_randSeed = 0;
    s_randSeedEpoch = 1;
    s_timeunit = VL_TIME_UNIT;  // Initial value until overriden by _Vconfigure
    s_timeprecision = VL_TIME_PRECISION;  // Initial value until overriden by _Vconfigure
}

void Verilated::NonSerialized::setup() { s_profThreadsFilenamep = strdup("profile_threads.dat"); }
void Verilated::NonSerialized::teardown() {
    if (s_profThreadsFilenamep) {
        VL_DO_CLEAR(free(const_cast<char*>(s_profThreadsFilenamep)),
                    s_profThreadsFilenamep = nullptr);
    }
}

size_t Verilated::serialized2Size() VL_PURE { return sizeof(VerilatedImp::s_s.v.m_ser); }
void* Verilated::serialized2Ptr() VL_MT_UNSAFE { return &VerilatedImp::s_s.v.m_ser; }

//===========================================================================
// Random -- Mostly called at init time, so not inline.

static vluint32_t vl_sys_rand32() VL_MT_UNSAFE {
    // Return random 32-bits using system library.
    // Used only to construct seed for Verilator's PNRG.
    static VerilatedMutex s_mutex;
    const VerilatedLockGuard lock(s_mutex);  // Otherwise rand is unsafe
#if defined(_WIN32) && !defined(__CYGWIN__)
    // Windows doesn't have lrand48(), although Cygwin does.
    return (rand() << 16) ^ rand();
#else
    return (lrand48() << 16) ^ lrand48();
#endif
}

vluint64_t vl_rand64() VL_MT_SAFE {
    static VL_THREAD_LOCAL vluint32_t t_seedEpoch = 0;
    static VL_THREAD_LOCAL vluint64_t t_state[2];
    // For speed, we use a thread-local epoch number to know when to reseed
    if (VL_UNLIKELY(t_seedEpoch != Verilated::randSeedEpoch())) {
        // Set epoch before state, in case races with new seeding
        t_seedEpoch = Verilated::randSeedEpoch();
        t_state[0] = Verilated::randSeedDefault64();
        t_state[1] = t_state[0];
        // Fix state as algorithm is slow to randomize if many zeros
        // This causes a loss of ~ 1 bit of seed entropy, no big deal
        if (VL_COUNTONES_I(t_state[0]) < 10) t_state[0] = ~t_state[0];
        if (VL_COUNTONES_I(t_state[1]) < 10) t_state[1] = ~t_state[1];
    }
    // Xoroshiro128+ algorithm
    vluint64_t result = t_state[0] + t_state[1];
    t_state[1] ^= t_state[0];
    t_state[0] = (((t_state[0] << 55) | (t_state[0] >> 9)) ^ t_state[1] ^ (t_state[1] << 14));
    t_state[1] = (t_state[1] << 36) | (t_state[1] >> 28);
    return result;
}

#ifndef VL_NO_LEGACY
// VL_RANDOM_W currently unused as $random always 32 bits, left for backwards compatibility
// LCOV_EXCL_START
WDataOutP VL_RANDOM_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i = 0; i < VL_WORDS_I(obits) - 1; ++i) outwp[i] = vl_rand64();
    outwp[VL_WORDS_I(obits) - 1] = vl_rand64() & VL_MASK_E(obits);
    return outwp;
}
// LCOV_EXCL_STOP
#endif

IData VL_RANDOM_SEEDED_II(int obits, IData seed) VL_MT_SAFE {
    Verilated::randSeed(static_cast<int>(seed));
    return VL_RANDOM_I(obits);
}

IData VL_RAND_RESET_I(int obits) VL_MT_SAFE {
    if (Verilated::randReset() == 0) return 0;
    IData data = ~0;
    if (Verilated::randReset() != 1) {  // if 2, randomize
        data = VL_RANDOM_I(obits);
    }
    data &= VL_MASK_I(obits);
    return data;
}
QData VL_RAND_RESET_Q(int obits) VL_MT_SAFE {
    if (Verilated::randReset() == 0) return 0;
    QData data = ~0ULL;
    if (Verilated::randReset() != 1) {  // if 2, randomize
        data = VL_RANDOM_Q(obits);
    }
    data &= VL_MASK_Q(obits);
    return data;
}
WDataOutP VL_RAND_RESET_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i = 0; i < VL_WORDS_I(obits) - 1; ++i) outwp[i] = VL_RAND_RESET_I(32);
    outwp[VL_WORDS_I(obits) - 1] = VL_RAND_RESET_I(32) & VL_MASK_E(obits);
    return outwp;
}

WDataOutP VL_ZERO_RESET_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i = 0; i < VL_WORDS_I(obits); ++i) outwp[i] = 0;
    return outwp;
}

//===========================================================================
// Debug

void _VL_DEBUG_PRINT_W(int lbits, WDataInP iwp) VL_MT_SAFE {
    VL_PRINTF_MT("  Data: w%d: ", lbits);
    for (int i = VL_WORDS_I(lbits) - 1; i >= 0; --i) VL_PRINTF_MT("%08x ", iwp[i]);
    VL_PRINTF_MT("\n");
}

//===========================================================================
// Slow math

WDataOutP _vl_moddiv_w(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp,
                       bool is_modulus) VL_MT_SAFE {
    // See Knuth Algorithm D.  Computes u/v = q.r
    // This isn't massively tuned, as wide division is rare
    // for debug see V3Number version
    // Requires clean input
    int words = VL_WORDS_I(lbits);
    for (int i = 0; i < words; ++i) owp[i] = 0;
    // Find MSB and check for zero.
    int umsbp1 = VL_MOSTSETBITP1_W(words, lwp);  // dividend
    int vmsbp1 = VL_MOSTSETBITP1_W(words, rwp);  // divisor
    if (VL_UNLIKELY(vmsbp1 == 0)  // rwp==0 so division by zero.  Return 0.
        || VL_UNLIKELY(umsbp1 == 0)) {  // 0/x so short circuit and return 0
        return owp;
    }

    int uw = VL_WORDS_I(umsbp1);  // aka "m" in the algorithm
    int vw = VL_WORDS_I(vmsbp1);  // aka "n" in the algorithm

    if (vw == 1) {  // Single divisor word breaks rest of algorithm
        vluint64_t k = 0;
        for (int j = uw - 1; j >= 0; --j) {
            vluint64_t unw64 = ((k << 32ULL) + static_cast<vluint64_t>(lwp[j]));
            owp[j] = unw64 / static_cast<vluint64_t>(rwp[0]);
            k = unw64 - static_cast<vluint64_t>(owp[j]) * static_cast<vluint64_t>(rwp[0]);
        }
        if (is_modulus) {
            owp[0] = k;
            for (int i = 1; i < words; ++i) owp[i] = 0;
        }
        return owp;
    }

    // +1 word as we may shift during normalization
    vluint32_t un[VL_MULS_MAX_WORDS + 1];  // Fixed size, as MSVC++ doesn't allow [words] here
    vluint32_t vn[VL_MULS_MAX_WORDS + 1];  // v normalized

    // Zero for ease of debugging and to save having to zero for shifts
    // Note +1 as loop will use extra word
    for (int i = 0; i < words + 1; ++i) { un[i] = vn[i] = 0; }

    // Algorithm requires divisor MSB to be set
    // Copy and shift to normalize divisor so MSB of vn[vw-1] is set
    int s = 31 - VL_BITBIT_I(vmsbp1 - 1);  // shift amount (0...31)
    vluint32_t shift_mask = s ? 0xffffffff : 0;  // otherwise >> 32 won't mask the value
    for (int i = vw - 1; i > 0; --i) {
        vn[i] = (rwp[i] << s) | (shift_mask & (rwp[i - 1] >> (32 - s)));
    }
    vn[0] = rwp[0] << s;

    // Copy and shift dividend by same amount; may set new upper word
    if (s) {
        un[uw] = lwp[uw - 1] >> (32 - s);
    } else {
        un[uw] = 0;
    }
    for (int i = uw - 1; i > 0; --i) {
        un[i] = (lwp[i] << s) | (shift_mask & (lwp[i - 1] >> (32 - s)));
    }
    un[0] = lwp[0] << s;

    // Main loop
    for (int j = uw - vw; j >= 0; --j) {
        // Estimate
        vluint64_t unw64 = (static_cast<vluint64_t>(un[j + vw]) << 32ULL
                            | static_cast<vluint64_t>(un[j + vw - 1]));
        vluint64_t qhat = unw64 / static_cast<vluint64_t>(vn[vw - 1]);
        vluint64_t rhat = unw64 - qhat * static_cast<vluint64_t>(vn[vw - 1]);

    again:
        if (qhat >= 0x100000000ULL || ((qhat * vn[vw - 2]) > ((rhat << 32ULL) + un[j + vw - 2]))) {
            qhat = qhat - 1;
            rhat = rhat + vn[vw - 1];
            if (rhat < 0x100000000ULL) goto again;
        }

        vlsint64_t t = 0;  // Must be signed
        vluint64_t k = 0;
        for (int i = 0; i < vw; ++i) {
            vluint64_t p = qhat * vn[i];  // Multiply by estimate
            t = un[i + j] - k - (p & 0xFFFFFFFFULL);  // Subtract
            un[i + j] = t;
            k = (p >> 32ULL) - (t >> 32ULL);
        }
        t = un[j + vw] - k;
        un[j + vw] = t;
        owp[j] = qhat;  // Save quotient digit

        if (t < 0) {
            // Over subtracted; correct by adding back
            owp[j]--;
            k = 0;
            for (int i = 0; i < vw; ++i) {
                t = static_cast<vluint64_t>(un[i + j]) + static_cast<vluint64_t>(vn[i]) + k;
                un[i + j] = t;
                k = t >> 32ULL;
            }
            un[j + vw] = un[j + vw] + k;
        }
    }

    if (is_modulus) {  // modulus
        // Need to reverse normalization on copy to output
        for (int i = 0; i < vw; ++i) {
            owp[i] = (un[i] >> s) | (shift_mask & (un[i + 1] << (32 - s)));
        }
        for (int i = vw; i < words; ++i) owp[i] = 0;
        return owp;
    } else {  // division
        return owp;
    }
}

WDataOutP VL_POW_WWW(int obits, int, int rbits, WDataOutP owp, WDataInP lwp,
                     WDataInP rwp) VL_MT_SAFE {
    // obits==lbits, rbits can be different
    owp[0] = 1;
    for (int i = 1; i < VL_WORDS_I(obits); i++) owp[i] = 0;
    // cppcheck-suppress variableScope
    WData powstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    WData lastpowstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    WData lastoutstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    // cppcheck-suppress variableScope
    VL_ASSIGN_W(obits, powstore, lwp);
    for (int bit = 0; bit < rbits; bit++) {
        if (bit > 0) {  // power = power*power
            VL_ASSIGN_W(obits, lastpowstore, powstore);
            VL_MUL_W(VL_WORDS_I(obits), powstore, lastpowstore, lastpowstore);
        }
        if (VL_BITISSET_W(rwp, bit)) {  // out *= power
            VL_ASSIGN_W(obits, lastoutstore, owp);
            VL_MUL_W(VL_WORDS_I(obits), owp, lastoutstore, powstore);
        }
    }
    return owp;
}
WDataOutP VL_POW_WWQ(int obits, int lbits, int rbits, WDataOutP owp, WDataInP lwp,
                     QData rhs) VL_MT_SAFE {
    WData rhsw[VL_WQ_WORDS_E];
    VL_SET_WQ(rhsw, rhs);
    return VL_POW_WWW(obits, lbits, rbits, owp, lwp, rhsw);
}
QData VL_POW_QQW(int, int, int rbits, QData lhs, WDataInP rwp) VL_MT_SAFE {
    // Skip check for rhs == 0, as short-circuit doesn't save time
    if (VL_UNLIKELY(lhs == 0)) return 0;
    QData power = lhs;
    QData out = 1ULL;
    for (int bit = 0; bit < rbits; ++bit) {
        if (bit > 0) power = power * power;
        if (VL_BITISSET_W(rwp, bit)) out *= power;
    }
    return out;
}

WDataOutP VL_POWSS_WWW(int obits, int, int rbits, WDataOutP owp, WDataInP lwp, WDataInP rwp,
                       bool lsign, bool rsign) VL_MT_SAFE {
    // obits==lbits, rbits can be different
    if (rsign && VL_SIGN_W(rbits, rwp)) {
        int words = VL_WORDS_I(obits);
        VL_ZERO_W(obits, owp);
        EData lor = 0;  // 0=all zeros, ~0=all ones, else mix
        for (int i = 1; i < (words - 1); ++i) { lor |= lwp[i]; }
        lor |= ((lwp[words - 1] == VL_MASK_E(rbits)) ? ~VL_EUL(0) : 0);
        if (lor == 0 && lwp[0] == 0) {  // "X" so return 0
            return owp;
        } else if (lor == 0 && lwp[0] == 1) {  // 1
            owp[0] = 1;
            return owp;
        } else if (lsign && lor == ~VL_EUL(0) && lwp[0] == ~VL_EUL(0)) {  // -1
            if (rwp[0] & 1) {  // -1^odd=-1
                return VL_ALLONES_W(obits, owp);
            } else {  // -1^even=1
                owp[0] = 1;
                return owp;
            }
        }
        return owp;
    }
    return VL_POW_WWW(obits, rbits, rbits, owp, lwp, rwp);
}
WDataOutP VL_POWSS_WWQ(int obits, int lbits, int rbits, WDataOutP owp, WDataInP lwp, QData rhs,
                       bool lsign, bool rsign) VL_MT_SAFE {
    WData rhsw[VL_WQ_WORDS_E];
    VL_SET_WQ(rhsw, rhs);
    return VL_POWSS_WWW(obits, lbits, rbits, owp, lwp, rhsw, lsign, rsign);
}
QData VL_POWSS_QQW(int obits, int, int rbits, QData lhs, WDataInP rwp, bool lsign,
                   bool rsign) VL_MT_SAFE {
    // Skip check for rhs == 0, as short-circuit doesn't save time
    if (rsign && VL_SIGN_W(rbits, rwp)) {
        if (lhs == 0) {
            return 0;  // "X"
        } else if (lhs == 1) {
            return 1;
        } else if (lsign && lhs == VL_MASK_Q(obits)) {  // -1
            if (rwp[0] & 1) {
                return VL_MASK_Q(obits);  // -1^odd=-1
            } else {
                return 1;  // -1^even=1
            }
        }
        return 0;
    }
    return VL_POW_QQW(obits, rbits, rbits, lhs, rwp);
}

double VL_ITOR_D_W(int lbits, WDataInP lwp) VL_PURE {
    int ms_word = VL_WORDS_I(lbits) - 1;
    for (; !lwp[ms_word] && ms_word > 0;) --ms_word;
    if (ms_word == 0) return static_cast<double>(lwp[0]);
    if (ms_word == 1) return static_cast<double>(VL_SET_QW(lwp));
    // We need 53 bits of mantissa, which might mean looking at 3 words
    // namely ms_word, ms_word-1 and ms_word-2
    EData ihi = lwp[ms_word];
    EData imid = lwp[ms_word - 1];
    EData ilo = lwp[ms_word - 2];
    double hi = static_cast<double>(ihi) * exp2(2 * VL_EDATASIZE);
    double mid = static_cast<double>(imid) * exp2(VL_EDATASIZE);
    double lo = static_cast<double>(ilo);
    double d = (hi + mid + lo) * exp2(VL_EDATASIZE * (ms_word - 2));
    return d;
}
double VL_ISTOR_D_W(int lbits, WDataInP lwp) VL_PURE {
    if (!VL_SIGN_W(lbits, lwp)) return VL_ITOR_D_W(lbits, lwp);
    vluint32_t pos[VL_MULS_MAX_WORDS + 1];  // Fixed size, as MSVC++ doesn't allow [words] here
    VL_NEGATE_W(VL_WORDS_I(lbits), pos, lwp);
    _VL_CLEAN_INPLACE_W(lbits, pos);
    return -VL_ITOR_D_W(lbits, pos);
}

//===========================================================================
// Formatting

/// Output a string representation of a wide number
std::string VL_DECIMAL_NW(int width, WDataInP lwp) VL_MT_SAFE {
    int maxdecwidth = (width + 3) * 4 / 3;
    // Or (maxdecwidth+7)/8], but can't have more than 4 BCD bits per word
    WData bcd[VL_VALUE_STRING_MAX_WIDTH / 4 + 2];
    VL_ZERO_RESET_W(maxdecwidth, bcd);
    WData tmp[VL_VALUE_STRING_MAX_WIDTH / 4 + 2];
    WData tmp2[VL_VALUE_STRING_MAX_WIDTH / 4 + 2];
    int from_bit = width - 1;
    // Skip all leading zeros
    for (; from_bit >= 0 && !(VL_BITRSHIFT_W(lwp, from_bit) & 1); --from_bit) {}
    // Double-dabble algorithm
    for (; from_bit >= 0; --from_bit) {
        // Any digits >= 5 need an add 3 (via tmp)
        for (int nibble_bit = 0; nibble_bit < maxdecwidth; nibble_bit += 4) {
            if ((VL_BITRSHIFT_W(bcd, nibble_bit) & 0xf) >= 5) {
                VL_ZERO_RESET_W(maxdecwidth, tmp2);
                tmp2[VL_BITWORD_E(nibble_bit)] |= VL_EUL(0x3) << VL_BITBIT_E(nibble_bit);
                VL_ASSIGN_W(maxdecwidth, tmp, bcd);
                VL_ADD_W(VL_WORDS_I(maxdecwidth), bcd, tmp, tmp2);
            }
        }
        // Shift; bcd = bcd << 1
        VL_ASSIGN_W(maxdecwidth, tmp, bcd);
        VL_SHIFTL_WWI(maxdecwidth, maxdecwidth, 32, bcd, tmp, 1);
        // bcd[0] = lwp[from_bit]
        if (VL_BITISSET_W(lwp, from_bit)) bcd[0] |= 1;
    }
    std::string output;
    int lsb = (maxdecwidth - 1) & ~3;
    for (; lsb > 0; lsb -= 4) {  // Skip leading zeros
        if (VL_BITRSHIFT_W(bcd, lsb) & 0xf) break;
    }
    for (; lsb >= 0; lsb -= 4) {
        output += ('0' + (VL_BITRSHIFT_W(bcd, lsb) & 0xf));  // 0..9
    }
    return output;
}

std::string _vl_vsformat_time(char* tmp, double ld, bool left, size_t width) {
    // Double may lose precision, but sc_time_stamp has similar limit
    std::string suffix = VerilatedImp::timeFormatSuffix();
    int userUnits = VerilatedImp::timeFormatUnits();  // 0..-15
    int fracDigits = VerilatedImp::timeFormatPrecision();  // 0..N
    int prec = Verilated::timeprecision();  // 0..-15
    int shift = prec - userUnits + fracDigits;  // 0..-15
    double shiftd = vl_time_multiplier(shift);
    double scaled = ld * shiftd;
    QData fracDiv = static_cast<QData>(vl_time_multiplier(fracDigits));
    QData whole = static_cast<QData>(scaled) / fracDiv;
    QData fraction = static_cast<QData>(scaled) % fracDiv;
    int digits = 0;
    if (!fracDigits) {
        digits = sprintf(tmp, "%" VL_PRI64 "u%s", whole, suffix.c_str());
    } else {
        digits = sprintf(tmp, "%" VL_PRI64 "u.%0*" VL_PRI64 "u%s", whole, fracDigits, fraction,
                         suffix.c_str());
    }
    int needmore = width - digits;
    std::string padding;
    if (needmore > 0) padding.append(needmore, ' ');  // Pad with spaces
    return left ? (tmp + padding) : (padding + tmp);
}

// Do a va_arg returning a quad, assuming input argument is anything less than wide
#define _VL_VA_ARG_Q(ap, bits) (((bits) <= VL_IDATASIZE) ? va_arg(ap, IData) : va_arg(ap, QData))

void _vl_vsformat(std::string& output, const char* formatp, va_list ap) VL_MT_SAFE {
    // Format a Verilog $write style format into the output list
    // The format must be pre-processed (and lower cased) by Verilator
    // Arguments are in "width, arg-value (or WDataIn* if wide)" form
    //
    // Note uses a single buffer internally; presumes only one usage per printf
    // Note also assumes variables < 64 are not wide, this assumption is
    // sometimes not true in low-level routines written here in verilated.cpp
    static VL_THREAD_LOCAL char t_tmp[VL_VALUE_STRING_MAX_WIDTH];
    const char* pctp = nullptr;  // Most recent %##.##g format
    bool inPct = false;
    bool widthSet = false;
    bool left = false;
    size_t width = 0;
    for (const char* pos = formatp; *pos; ++pos) {
        if (!inPct && pos[0] == '%') {
            pctp = pos;
            inPct = true;
            widthSet = false;
            width = 0;
        } else if (!inPct) {  // Normal text
            // Fast-forward to next escape and add to output
            const char* ep = pos;
            while (ep[0] && ep[0] != '%') ep++;
            if (ep != pos) {
                output.append(pos, ep - pos);
                pos += ep - pos - 1;
            }
        } else {  // Format character
            inPct = false;
            char fmt = pos[0];
            switch (fmt) {
            case '0':  // FALLTHRU
            case '1':  // FALLTHRU
            case '2':  // FALLTHRU
            case '3':  // FALLTHRU
            case '4':  // FALLTHRU
            case '5':  // FALLTHRU
            case '6':  // FALLTHRU
            case '7':  // FALLTHRU
            case '8':  // FALLTHRU
            case '9':
                inPct = true;  // Get more digits
                widthSet = true;
                width = width * 10 + (fmt - '0');
                break;
            case '-':
                left = true;
                inPct = true;  // Get more digits
                break;
            case '.':
                inPct = true;  // Get more digits
                break;
            case '%':  //
                output += '%';
                break;
            case 'N': {  // "C" string with name of module, add . if needed
                const char* cstrp = va_arg(ap, const char*);
                if (VL_LIKELY(*cstrp)) {
                    output += cstrp;
                    output += '.';
                }
                break;
            }
            case 'S': {  // "C" string
                const char* cstrp = va_arg(ap, const char*);
                output += cstrp;
                break;
            }
            case '@': {  // Verilog/C++ string
                va_arg(ap, int);  // # bits is ignored
                const std::string* cstrp = va_arg(ap, const std::string*);
                std::string padding;
                if (width > cstrp->size()) padding.append(width - cstrp->size(), ' ');
                output += left ? (*cstrp + padding) : (padding + *cstrp);
                break;
            }
            case 'e':
            case 'f':
            case 'g':
            case '^': {  // Realtime
                const int lbits = va_arg(ap, int);
                double d = va_arg(ap, double);
                if (lbits) {}  // UNUSED - always 64
                if (fmt == '^') {  // Realtime
                    if (!widthSet) width = VerilatedImp::timeFormatWidth();
                    output += _vl_vsformat_time(t_tmp, d, left, width);
                } else {
                    std::string fmts(pctp, pos - pctp + 1);
                    sprintf(t_tmp, fmts.c_str(), d);
                    output += t_tmp;
                }
                break;
            }
            default: {
                // Deal with all read-and-print somethings
                const int lbits = va_arg(ap, int);
                QData ld = 0;
                WData qlwp[VL_WQ_WORDS_E];
                WDataInP lwp = nullptr;
                if (lbits <= VL_QUADSIZE) {
                    ld = _VL_VA_ARG_Q(ap, lbits);
                    VL_SET_WQ(qlwp, ld);
                    lwp = qlwp;
                } else {
                    lwp = va_arg(ap, WDataInP);
                    ld = lwp[0];
                }
                int lsb = lbits - 1;
                if (widthSet && width == 0) {
                    while (lsb && !VL_BITISSET_W(lwp, lsb)) --lsb;
                }
                switch (fmt) {
                case 'c': {
                    IData charval = ld & 0xff;
                    output += static_cast<char>(charval);
                    break;
                }
                case 's': {
                    std::string field;
                    for (; lsb >= 0; --lsb) {
                        lsb = (lsb / 8) * 8;  // Next digit
                        IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xff;
                        field += (charval == 0) ? ' ' : charval;
                    }
                    std::string padding;
                    if (width > field.size()) padding.append(width - field.size(), ' ');
                    output += left ? (field + padding) : (padding + field);
                    break;
                }
                case 'd': {  // Signed decimal
                    int digits = 0;
                    std::string append;
                    if (lbits <= VL_QUADSIZE) {
                        digits = sprintf(t_tmp, "%" VL_PRI64 "d",
                                         static_cast<vlsint64_t>(VL_EXTENDS_QQ(lbits, lbits, ld)));
                        append = t_tmp;
                    } else {
                        if (VL_SIGN_E(lbits, lwp[VL_WORDS_I(lbits) - 1])) {
                            WData neg[VL_VALUE_STRING_MAX_WIDTH / 4 + 2];
                            VL_NEGATE_W(VL_WORDS_I(lbits), neg, lwp);
                            append = std::string("-") + VL_DECIMAL_NW(lbits, neg);
                        } else {
                            append = VL_DECIMAL_NW(lbits, lwp);
                        }
                        digits = append.length();
                    }
                    int needmore = width - digits;
                    std::string padding;
                    if (needmore > 0) {
                        if (pctp && pctp[0] && pctp[1] == '0') {  // %0
                            padding.append(needmore, '0');  // Pre-pad zero
                        } else {
                            padding.append(needmore, ' ');  // Pre-pad spaces
                        }
                    }
                    output += left ? (append + padding) : (padding + append);
                    break;
                }
                case '#': {  // Unsigned decimal
                    int digits = 0;
                    std::string append;
                    if (lbits <= VL_QUADSIZE) {
                        digits = sprintf(t_tmp, "%" VL_PRI64 "u", ld);
                        append = t_tmp;
                    } else {
                        append = VL_DECIMAL_NW(lbits, lwp);
                        digits = append.length();
                    }
                    int needmore = width - digits;
                    std::string padding;
                    if (needmore > 0) {
                        if (pctp && pctp[0] && pctp[1] == '0') {  // %0
                            padding.append(needmore, '0');  // Pre-pad zero
                        } else {
                            padding.append(needmore, ' ');  // Pre-pad spaces
                        }
                    }
                    output += left ? (append + padding) : (padding + append);
                    break;
                }
                case 't': {  // Time
                    if (!widthSet) width = VerilatedImp::timeFormatWidth();
                    output += _vl_vsformat_time(t_tmp, static_cast<double>(ld), left, width);
                    break;
                }
                case 'b':
                    for (; lsb >= 0; --lsb) output += (VL_BITRSHIFT_W(lwp, lsb) & 1) + '0';
                    break;
                case 'o':
                    for (; lsb >= 0; --lsb) {
                        lsb = (lsb / 3) * 3;  // Next digit
                        // Octal numbers may span more than one wide word,
                        // so we need to grab each bit separately and check for overrun
                        // Octal is rare, so we'll do it a slow simple way
                        output += static_cast<char>(
                            '0' + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb + 0)) ? 1 : 0)
                            + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb + 1)) ? 2 : 0)
                            + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb + 2)) ? 4 : 0));
                    }
                    break;
                case 'u':
                case 'z': {  // Packed 4-state
                    const bool is_4_state = (fmt == 'z');
                    output.reserve(output.size() + ((is_4_state ? 2 : 1) * VL_WORDS_I(lbits)));
                    int bytes_to_go = VL_BYTES_I(lbits);
                    int bit = 0;
                    while (bytes_to_go > 0) {
                        const int wr_bytes = std::min(4, bytes_to_go);
                        for (int byte = 0; byte < wr_bytes; byte++, bit += 8)
                            output += static_cast<char>(VL_BITRSHIFT_W(lwp, bit) & 0xff);
                        output.append(4 - wr_bytes, static_cast<char>(0));
                        if (is_4_state) output.append(4, static_cast<char>(0));
                        bytes_to_go -= wr_bytes;
                    }
                    break;
                }
                case 'v':  // Strength; assume always strong
                    for (lsb = lbits - 1; lsb >= 0; --lsb) {
                        if (VL_BITRSHIFT_W(lwp, lsb) & 1) {
                            output += "St1 ";
                        } else {
                            output += "St0 ";
                        }
                    }
                    break;
                case 'x':
                    for (; lsb >= 0; --lsb) {
                        lsb = (lsb / 4) * 4;  // Next digit
                        IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xf;
                        output += "0123456789abcdef"[charval];
                    }
                    break;
                default: {  // LCOV_EXCL_START
                    std::string msg = std::string("Unknown _vl_vsformat code: ") + pos[0];
                    VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
                    break;
                }  // LCOV_EXCL_STOP
                }  // switch
            }
            }  // switch
        }
    }
}

static inline bool _vl_vsss_eof(FILE* fp, int floc) VL_MT_SAFE {
    if (fp) {
        return feof(fp) ? true : false;  // true : false to prevent MSVC++ warning
    } else {
        return floc < 0;
    }
}
static inline void _vl_vsss_advance(FILE* fp, int& floc) VL_MT_SAFE {
    if (fp) {
        fgetc(fp);
    } else {
        floc -= 8;
    }
}
static inline int _vl_vsss_peek(FILE* fp, int& floc, WDataInP fromp,
                                const std::string& fstr) VL_MT_SAFE {
    // Get a character without advancing
    if (fp) {
        int data = fgetc(fp);
        if (data == EOF) return EOF;
        ungetc(data, fp);
        return data;
    } else {
        if (floc < 0) return EOF;
        floc = floc & ~7;  // Align to closest character
        if (fromp == nullptr) {
            return fstr[fstr.length() - 1 - (floc >> 3)];
        } else {
            return VL_BITRSHIFT_W(fromp, floc) & 0xff;
        }
    }
}
static inline void _vl_vsss_skipspace(FILE* fp, int& floc, WDataInP fromp,
                                      const std::string& fstr) VL_MT_SAFE {
    while (true) {
        int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c == EOF || !isspace(c)) return;
        _vl_vsss_advance(fp, floc);
    }
}
static inline void _vl_vsss_read_str(FILE* fp, int& floc, WDataInP fromp, const std::string& fstr,
                                     char* tmpp, const char* acceptp) VL_MT_SAFE {
    // Read into tmp, consisting of characters from acceptp list
    char* cp = tmpp;
    while (true) {
        int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c == EOF || isspace(c)) break;
        if (acceptp && nullptr == strchr(acceptp, c)) break;  // String - allow anything
        if (acceptp) c = tolower(c);  // Non-strings we'll simplify
        *cp++ = c;
        _vl_vsss_advance(fp, floc);
    }
    *cp++ = '\0';
    // VL_DBG_MSGF(" _read got='"<<tmpp<<"'\n");
}
static inline char* _vl_vsss_read_bin(FILE* fp, int& floc, WDataInP fromp, const std::string& fstr,
                                      char* beginp, std::size_t n, bool inhibit = false) {
    // Variant of _vl_vsss_read_str using the same underlying I/O functions but optimized
    // specifically for block reads of N bytes (read operations are not demarcated by
    // whitespace). In the fp case, except descriptor to have been opened in binary mode.
    while (n-- > 0) {
        const int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c == EOF) return nullptr;
        if (!inhibit) *beginp++ = c;
        _vl_vsss_advance(fp, floc);
    }
    return beginp;
}
static inline void _vl_vsss_setbit(WDataOutP owp, int obits, int lsb, int nbits,
                                   IData ld) VL_MT_SAFE {
    for (; nbits && lsb < obits; nbits--, lsb++, ld >>= 1) {
        VL_ASSIGNBIT_WI(0, lsb, owp, ld & 1);
    }
}
static inline void _vl_vsss_based(WDataOutP owp, int obits, int baseLog2, const char* strp,
                                  size_t posstart, size_t posend) VL_MT_SAFE {
    // Read in base "2^^baseLog2" digits from strp[posstart..posend-1] into owp of size obits.
    int lsb = 0;
    for (int i = 0, pos = static_cast<int>(posend) - 1;
         i < obits && pos >= static_cast<int>(posstart); --pos) {
        // clang-format off
        switch (tolower (strp[pos])) {
        case 'x': case 'z': case '?':  // FALLTHRU
        case '0': lsb += baseLog2; break;
        case '1': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  1); lsb += baseLog2; break;
        case '2': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  2); lsb += baseLog2; break;
        case '3': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  3); lsb += baseLog2; break;
        case '4': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  4); lsb += baseLog2; break;
        case '5': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  5); lsb += baseLog2; break;
        case '6': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  6); lsb += baseLog2; break;
        case '7': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  7); lsb += baseLog2; break;
        case '8': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  8); lsb += baseLog2; break;
        case '9': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  9); lsb += baseLog2; break;
        case 'a': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 10); lsb += baseLog2; break;
        case 'b': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 11); lsb += baseLog2; break;
        case 'c': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 12); lsb += baseLog2; break;
        case 'd': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 13); lsb += baseLog2; break;
        case 'e': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 14); lsb += baseLog2; break;
        case 'f': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 15); lsb += baseLog2; break;
        case '_': break;
        }
        // clang-format on
    }
}

IData _vl_vsscanf(FILE* fp,  // If a fscanf
                  int fbits, WDataInP fromp,  // Else if a sscanf
                  const std::string& fstr,  // if a sscanf to string
                  const char* formatp, va_list ap) VL_MT_SAFE {
    // Read a Verilog $sscanf/$fscanf style format into the output list
    // The format must be pre-processed (and lower cased) by Verilator
    // Arguments are in "width, arg-value (or WDataIn* if wide)" form
    static VL_THREAD_LOCAL char t_tmp[VL_VALUE_STRING_MAX_WIDTH];
    int floc = fbits - 1;
    IData got = 0;
    bool inPct = false;
    bool inIgnore = false;
    const char* pos = formatp;
    for (; *pos && !_vl_vsss_eof(fp, floc); ++pos) {
        // VL_DBG_MSGF("_vlscan fmt='"<<pos[0]<<"' floc="<<floc<<" file='"<<_vl_vsss_peek(fp, floc,
        // fromp, fstr)<<"'\n");
        if (!inPct && pos[0] == '%') {
            inPct = true;
            inIgnore = false;
        } else if (!inPct && isspace(pos[0])) {  // Format spaces
            while (isspace(pos[1])) pos++;
            _vl_vsss_skipspace(fp, floc, fromp, fstr);
        } else if (!inPct) {  // Expected Format
            _vl_vsss_skipspace(fp, floc, fromp, fstr);
            int c = _vl_vsss_peek(fp, floc, fromp, fstr);
            if (c != pos[0]) goto done;
            _vl_vsss_advance(fp, floc);
        } else {  // Format character
            // Skip loading spaces
            inPct = false;
            char fmt = pos[0];
            switch (fmt) {
            case '%': {
                int c = _vl_vsss_peek(fp, floc, fromp, fstr);
                if (c != '%') goto done;
                _vl_vsss_advance(fp, floc);
                break;
            }
            case '*':
                inPct = true;
                inIgnore = true;
                break;
            default: {
                // Deal with all read-and-scan somethings
                // Note LSBs are preserved if there's an overflow
                const int obits = inIgnore ? 0 : va_arg(ap, int);
                WData qowp[VL_WQ_WORDS_E];
                VL_SET_WQ(qowp, 0ULL);
                WDataOutP owp = qowp;
                if (obits == -1) {  // string
                    owp = nullptr;
                    if (VL_UNCOVERABLE(fmt != 's')) {
                        VL_FATAL_MT(
                            __FILE__, __LINE__, "",
                            "Internal: format other than %s is passed to string");  // LCOV_EXCL_LINE
                    }
                } else if (obits > VL_QUADSIZE) {
                    owp = va_arg(ap, WDataOutP);
                }

                for (int i = 0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
                switch (fmt) {
                case 'c': {
                    int c = _vl_vsss_peek(fp, floc, fromp, fstr);
                    if (c == EOF) goto done;
                    _vl_vsss_advance(fp, floc);
                    owp[0] = c;
                    break;
                }
                case 's': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, nullptr);
                    if (!t_tmp[0]) goto done;
                    if (owp) {
                        int lpos = (static_cast<int>(strlen(t_tmp))) - 1;
                        int lsb = 0;
                        for (int i = 0; i < obits && lpos >= 0; --lpos) {
                            _vl_vsss_setbit(owp, obits, lsb, 8, t_tmp[lpos]);
                            lsb += 8;
                        }
                    }
                    break;
                }
                case 'd': {  // Signed decimal
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "0123456789+-xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    vlsint64_t ld = 0;
                    sscanf(t_tmp, "%30" VL_PRI64 "d", &ld);
                    VL_SET_WQ(owp, ld);
                    break;
                }
                case 'f':
                case 'e':
                case 'g': {  // Real number
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "+-.0123456789eE");
                    if (!t_tmp[0]) goto done;
                    // cppcheck-suppress unusedStructMember  // It's used
                    union {
                        double r;
                        vlsint64_t ld;
                    } u;
                    u.r = strtod(t_tmp, nullptr);
                    VL_SET_WQ(owp, u.ld);
                    break;
                }
                case 't':  // FALLTHRU  // Time
                case '#': {  // Unsigned decimal
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "0123456789+-xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    QData ld = 0;
                    sscanf(t_tmp, "%30" VL_PRI64 "u", &ld);
                    VL_SET_WQ(owp, ld);
                    break;
                }
                case 'b': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "01xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 1, t_tmp, 0, strlen(t_tmp));
                    break;
                }
                case 'o': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "01234567xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 3, t_tmp, 0, strlen(t_tmp));
                    break;
                }
                case 'x': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp,
                                      "0123456789abcdefABCDEFxXzZ?_");
                    if (!t_tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 4, t_tmp, 0, strlen(t_tmp));
                    break;
                }
                case 'u': {
                    // Read packed 2-value binary data
                    const int bytes = VL_BYTES_I(obits);
                    char* out = reinterpret_cast<char*>(owp);
                    if (!_vl_vsss_read_bin(fp, floc, fromp, fstr, out, bytes)) goto done;
                    const int last = bytes % 4;
                    if (last != 0
                        && !_vl_vsss_read_bin(fp, floc, fromp, fstr, out, 4 - last, true))
                        goto done;
                    break;
                }
                case 'z': {
                    // Read packed 4-value binary data
                    char* out = reinterpret_cast<char*>(owp);
                    int bytes = VL_BYTES_I(obits);
                    while (bytes > 0) {
                        const int abytes = std::min(4, bytes);
                        // aval (4B) read {0, 1} state
                        out = _vl_vsss_read_bin(fp, floc, fromp, fstr, out, abytes);
                        if (!out) goto done;
                        // bval (4B) disregard {X, Z} state and align to new 8B boundary.
                        out = _vl_vsss_read_bin(fp, floc, fromp, fstr, out, 8 - abytes, true);
                        if (!out) goto done;
                        bytes -= abytes;
                    }
                    break;
                }
                default: {  // LCOV_EXCL_START
                    std::string msg = std::string("Unknown _vl_vsscanf code: ") + pos[0];
                    VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
                    break;
                }  // LCOV_EXCL_STOP

                }  // switch

                if (!inIgnore) ++got;
                // Reload data if non-wide (if wide, we put it in the right place directly)
                if (obits == 0) {  // Due to inIgnore
                } else if (obits == -1) {  // string
                    std::string* p = va_arg(ap, std::string*);
                    *p = t_tmp;
                } else if (obits <= VL_BYTESIZE) {
                    CData* p = va_arg(ap, CData*);
                    *p = owp[0];
                } else if (obits <= VL_SHORTSIZE) {
                    SData* p = va_arg(ap, SData*);
                    *p = owp[0];
                } else if (obits <= VL_IDATASIZE) {
                    IData* p = va_arg(ap, IData*);
                    *p = owp[0];
                } else if (obits <= VL_QUADSIZE) {
                    QData* p = va_arg(ap, QData*);
                    *p = VL_SET_QW(owp);
                }
            }
            }  // switch
        }
    }
done:
    return got;
}

//===========================================================================
// File I/O

FILE* VL_CVT_I_FP(IData lhs) VL_MT_SAFE {
    // Expected non-MCD case; returns null on MCD descriptors.
    return VerilatedImp::fdToFp(lhs);
}

void _VL_VINT_TO_STRING(int obits, char* destoutp, WDataInP sourcep) VL_MT_SAFE {
    // See also VL_DATA_TO_STRING_NW
    int lsb = obits - 1;
    bool start = true;
    char* destp = destoutp;
    for (; lsb >= 0; --lsb) {
        lsb = (lsb / 8) * 8;  // Next digit
        IData charval = VL_BITRSHIFT_W(sourcep, lsb) & 0xff;
        if (!start || charval) {
            *destp++ = (charval == 0) ? ' ' : charval;
            start = false;  // Drop leading 0s
        }
    }
    *destp = '\0';  // Terminate
    if (!start) {  // Drop trailing spaces
        while (isspace(*(destp - 1)) && destp > destoutp) *--destp = '\0';
    }
}

void _VL_STRING_TO_VINT(int obits, void* destp, size_t srclen, const char* srcp) VL_MT_SAFE {
    // Convert C string to Verilog format
    size_t bytes = VL_BYTES_I(obits);
    char* op = reinterpret_cast<char*>(destp);
    if (srclen > bytes) srclen = bytes;  // Don't overflow destination
    size_t i = 0;
    for (i = 0; i < srclen; ++i) { *op++ = srcp[srclen - 1 - i]; }
    for (; i < bytes; ++i) { *op++ = 0; }
}

static IData getLine(std::string& str, IData fpi, size_t maxLen) VL_MT_SAFE {
    str.clear();

    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;

    // We don't use fgets, as we must read \0s.
    while (str.size() < maxLen) {
        const int c = getc(fp);  // getc() is threadsafe
        if (c == EOF) break;
        str.push_back(c);
        if (c == '\n') break;
    }
    return str.size();
}

IData VL_FGETS_IXI(int obits, void* destp, IData fpi) VL_MT_SAFE {
    std::string str;
    const IData bytes = VL_BYTES_I(obits);
    IData got = getLine(str, fpi, bytes);

    if (VL_UNLIKELY(str.empty())) return 0;

    // V3Emit has static check that bytes < VL_TO_STRING_MAX_WORDS, but be safe
    if (VL_UNCOVERABLE(bytes < str.size())) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: fgets buffer overrun");  // LCOV_EXCL_LINE
    }

    _VL_STRING_TO_VINT(obits, destp, got, str.data());
    return got;
}

// declared in verilated_heavy.h
IData VL_FGETS_NI(std::string& dest, IData fpi) VL_MT_SAFE {
    return getLine(dest, fpi, std::numeric_limits<size_t>::max());
}

IData VL_FERROR_IN(IData, std::string& outputr) VL_MT_SAFE {
    // We ignore lhs/fpi - IEEE says "most recent error" so probably good enough
    IData ret = errno;
    outputr = std::string(::strerror(ret));
    return ret;
}

IData VL_FOPEN_NN(const std::string& filename, const std::string& mode) {
    return VerilatedImp::fdNew(filename.c_str(), mode.c_str());
}
IData VL_FOPEN_MCD_N(const std::string& filename) VL_MT_SAFE {
    return VerilatedImp::fdNewMcd(filename.c_str());
}

void VL_FFLUSH_I(IData fdi) VL_MT_SAFE { VerilatedImp::fdFlush(fdi); }
IData VL_FSEEK_I(IData fdi, IData offset, IData origin) VL_MT_SAFE {
    return VerilatedImp::fdSeek(fdi, offset, origin);
}
IData VL_FTELL_I(IData fdi) VL_MT_SAFE { return VerilatedImp::fdTell(fdi); }
void VL_FCLOSE_I(IData fdi) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    VerilatedImp::fdClose(fdi);
}

void VL_SFORMAT_X(int obits, CData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, SData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, IData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, QData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, void* destp, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, destp, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits_ignored, std::string& output, const char* formatp, ...) VL_MT_SAFE {
    if (obits_ignored) {}
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);
}

std::string VL_SFORMATF_NX(const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    return t_output;
}

void VL_WRITEF(const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    VL_PRINTF_MT("%s", t_output.c_str());
}

void VL_FWRITEF(IData fpi, const char* formatp, ...) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";

    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    VerilatedImp::fdWrite(fpi, t_output);
}

IData VL_FSCANF_IX(IData fpi, const char* formatp, ...) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;

    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(fp, 0, nullptr, "", formatp, ap);
    va_end(ap);
    return got;
}

IData VL_SSCANF_IIX(int lbits, IData ld, const char* formatp, ...) VL_MT_SAFE {
    WData fnw[VL_WQ_WORDS_E];
    VL_SET_WI(fnw, ld);

    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(nullptr, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IQX(int lbits, QData ld, const char* formatp, ...) VL_MT_SAFE {
    WData fnw[VL_WQ_WORDS_E];
    VL_SET_WQ(fnw, ld);

    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(nullptr, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IWX(int lbits, WDataInP lwp, const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(nullptr, lbits, lwp, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_INX(int, const std::string& ld, const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(nullptr, ld.length() * 8, nullptr, ld, formatp, ap);
    va_end(ap);
    return got;
}

IData VL_FREAD_I(int width, int array_lsb, int array_size, void* memp, IData fpi, IData start,
                 IData count) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;
    if (count > (array_size - (start - array_lsb))) count = array_size - (start - array_lsb);
    // Prep for reading
    IData read_count = 0;
    IData read_elements = 0;
    int start_shift = (width - 1) & ~7;  // bit+7:bit gets first character
    int shift = start_shift;
    // Read the data
    // We process a character at a time, as then we don't need to deal
    // with changing buffer sizes dynamically, etc.
    while (true) {
        int c = fgetc(fp);
        if (VL_UNLIKELY(c == EOF)) break;
        // Shift value in
        IData entry = read_elements + start - array_lsb;
        if (width <= 8) {
            CData* datap = &(reinterpret_cast<CData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= 16) {
            SData* datap = &(reinterpret_cast<SData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= VL_IDATASIZE) {
            IData* datap = &(reinterpret_cast<IData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= VL_QUADSIZE) {
            QData* datap = &(reinterpret_cast<QData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= ((static_cast<QData>(c) << static_cast<QData>(shift)) & VL_MASK_Q(width));
        } else {
            WDataOutP datap = &(reinterpret_cast<WDataOutP>(memp))[entry * VL_WORDS_I(width)];
            if (shift == start_shift) VL_ZERO_RESET_W(width, datap);
            datap[VL_BITWORD_E(shift)] |= (static_cast<EData>(c) << VL_BITBIT_E(shift));
        }
        // Prep for next
        ++read_count;
        shift -= 8;
        if (shift < 0) {
            shift = start_shift;
            ++read_elements;
            if (VL_UNLIKELY(read_elements >= count)) break;
        }
    }
    return read_count;
}

IData VL_SYSTEM_IQ(QData lhs) VL_MT_SAFE {
    WData lhsw[VL_WQ_WORDS_E];
    VL_SET_WQ(lhsw, lhs);
    return VL_SYSTEM_IW(VL_WQ_WORDS_E, lhsw);
}
IData VL_SYSTEM_IW(int lhswords, WDataInP lhsp) VL_MT_SAFE {
    char filenamez[VL_TO_STRING_MAX_WORDS * VL_EDATASIZE + 1];
    _VL_VINT_TO_STRING(lhswords * VL_EDATASIZE, filenamez, lhsp);
    int code = system(filenamez);  // Yes, system() is threadsafe
    return code >> 8;  // Want exit status
}

IData VL_TESTPLUSARGS_I(const char* formatp) VL_MT_SAFE {
    const std::string& match = VerilatedImp::argPlusMatch(formatp);
    return match.empty() ? 0 : 1;
}

IData VL_VALUEPLUSARGS_INW(int rbits, const std::string& ld, WDataOutP rwp) VL_MT_SAFE {
    std::string prefix;
    bool inPct = false;
    bool done = false;
    char fmt = ' ';
    for (const char* posp = ld.c_str(); !done && *posp; ++posp) {
        if (!inPct && posp[0] == '%') {
            inPct = true;
        } else if (!inPct) {  // Normal text
            prefix += *posp;
        } else {  // Format character
            switch (tolower(*posp)) {
            case '%':
                prefix += *posp;
                inPct = false;
                break;
            default:
                fmt = *posp;
                done = true;
                break;
            }
        }
    }

    const std::string& match = VerilatedImp::argPlusMatch(prefix.c_str());
    const char* dp = match.c_str() + 1 /*leading + */ + prefix.length();
    if (match.empty()) return 0;

    VL_ZERO_RESET_W(rbits, rwp);
    switch (tolower(fmt)) {
    case 'd': {
        vlsint64_t lld = 0;
        sscanf(dp, "%30" VL_PRI64 "d", &lld);
        VL_SET_WQ(rwp, lld);
        break;
    }
    case 'b': _vl_vsss_based(rwp, rbits, 1, dp, 0, strlen(dp)); break;
    case 'o': _vl_vsss_based(rwp, rbits, 3, dp, 0, strlen(dp)); break;
    case 'h':  // FALLTHRU
    case 'x': _vl_vsss_based(rwp, rbits, 4, dp, 0, strlen(dp)); break;
    case 's': {  // string/no conversion
        for (int i = 0, lsb = 0, posp = static_cast<int>(strlen(dp)) - 1; i < rbits && posp >= 0;
             --posp) {
            _vl_vsss_setbit(rwp, rbits, lsb, 8, dp[posp]);
            lsb += 8;
        }
        break;
    }
    case 'e': {
        double temp = 0.F;
        sscanf(dp, "%le", &temp);
        VL_SET_WQ(rwp, VL_CVT_Q_D(temp));
        break;
    }
    case 'f': {
        double temp = 0.F;
        sscanf(dp, "%lf", &temp);
        VL_SET_WQ(rwp, VL_CVT_Q_D(temp));
        break;
    }
    case 'g': {
        double temp = 0.F;
        sscanf(dp, "%lg", &temp);
        VL_SET_WQ(rwp, VL_CVT_Q_D(temp));
        break;
    }
    default:  // Other simulators simply return 0 in these cases and don't error out
        return 0;
    }
    _VL_CLEAN_INPLACE_W(rbits, rwp);
    return 1;
}
IData VL_VALUEPLUSARGS_INN(int, const std::string& ld, std::string& rdr) VL_MT_SAFE {
    std::string prefix;
    bool inPct = false;
    bool done = false;
    for (const char* posp = ld.c_str(); !done && *posp; ++posp) {
        if (!inPct && posp[0] == '%') {
            inPct = true;
        } else if (!inPct) {  // Normal text
            prefix += *posp;
        } else {  // Format character
            switch (tolower(*posp)) {
            case '%':
                prefix += *posp;
                inPct = false;
                break;
            default:  //
                done = true;
                break;
            }
        }
    }
    const std::string& match = VerilatedImp::argPlusMatch(prefix.c_str());
    const char* dp = match.c_str() + 1 /*leading + */ + prefix.length();
    if (match.empty()) return 0;
    rdr = std::string(dp);
    return 1;
}

const char* vl_mc_scan_plusargs(const char* prefixp) VL_MT_SAFE {
    const std::string& match = VerilatedImp::argPlusMatch(prefixp);
    static VL_THREAD_LOCAL char t_outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match.empty()) return nullptr;
    t_outstr[0] = '\0';
    strncat(t_outstr, match.c_str() + strlen(prefixp) + 1,  // +1 to skip the "+"
            VL_VALUE_STRING_MAX_WIDTH - 1);
    return t_outstr;
}

//===========================================================================
// Heavy string functions

std::string VL_TO_STRING(CData lhs) { return VL_SFORMATF_NX("'h%0x", 8, lhs); }
std::string VL_TO_STRING(SData lhs) { return VL_SFORMATF_NX("'h%0x", 16, lhs); }
std::string VL_TO_STRING(IData lhs) { return VL_SFORMATF_NX("'h%0x", 32, lhs); }
std::string VL_TO_STRING(QData lhs) { return VL_SFORMATF_NX("'h%0x", 64, lhs); }
std::string VL_TO_STRING_W(int words, WDataInP obj) {
    return VL_SFORMATF_NX("'h%0x", words * VL_EDATASIZE, obj);
}

std::string VL_TOLOWER_NN(const std::string& ld) VL_MT_SAFE {
    std::string out = ld;
    for (auto& cr : out) cr = tolower(cr);
    return out;
}
std::string VL_TOUPPER_NN(const std::string& ld) VL_MT_SAFE {
    std::string out = ld;
    for (auto& cr : out) cr = toupper(cr);
    return out;
}

std::string VL_CVT_PACK_STR_NW(int lwords, WDataInP lwp) VL_MT_SAFE {
    // See also _VL_VINT_TO_STRING
    char destout[VL_TO_STRING_MAX_WORDS * VL_EDATASIZE + 1];
    int obits = lwords * VL_EDATASIZE;
    int lsb = obits - 1;
    bool start = true;
    char* destp = destout;
    int len = 0;
    for (; lsb >= 0; --lsb) {
        lsb = (lsb / 8) * 8;  // Next digit
        IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xff;
        if (!start || charval) {
            *destp++ = (charval == 0) ? ' ' : charval;
            len++;
            start = false;  // Drop leading 0s
        }
    }
    return std::string(destout, len);
}

std::string VL_PUTC_N(const std::string& lhs, IData rhs, CData ths) VL_PURE {
    std::string lstring = lhs;
    const vlsint32_t rhs_s = rhs;  // To signed value
    // 6.16.2:str.putc(i, c) does not change the value when i < 0 || i >= str.len() || c == 0
    if (0 <= rhs_s && rhs < lhs.length() && ths != 0) lstring[rhs] = ths;
    return lstring;
}

CData VL_GETC_N(const std::string& lhs, IData rhs) VL_PURE {
    CData v = 0;
    const vlsint32_t rhs_s = rhs;  // To signed value
    // 6.16.3:str.getc(i) returns 0 if i < 0 || i >= str.len()
    if (0 <= rhs_s && rhs < lhs.length()) v = lhs[rhs];
    return v;
}

std::string VL_SUBSTR_N(const std::string& lhs, IData rhs, IData ths) VL_PURE {
    const vlsint32_t rhs_s = rhs;  // To signed value
    const vlsint32_t ths_s = ths;  // To signed value
    // 6.16.8:str.substr(i, j) returns an empty string when i < 0 || j < i || j >= str.len()
    if (rhs_s < 0 || ths_s < rhs_s || ths >= lhs.length()) return "";
    // Second parameter of std::string::substr(i, n) is length, not position as in SystemVerilog
    return lhs.substr(rhs, ths - rhs + 1);
}

IData VL_ATOI_N(const std::string& str, int base) VL_PURE {
    std::string str_mod = str;
    // IEEE 1800-2017 6.16.9 says '_' may exist.
    str_mod.erase(std::remove(str_mod.begin(), str_mod.end(), '_'), str_mod.end());

    errno = 0;
    auto v = std::strtol(str_mod.c_str(), nullptr, base);
    if (errno != 0) v = 0;
    return static_cast<IData>(v);
}

//===========================================================================
// Dumping

const char* vl_dumpctl_filenamep(bool setit, const std::string& filename) VL_MT_SAFE {
    // This function performs both accessing and setting so it's easy to make an in-function static
    static VL_THREAD_LOCAL std::string t_filename;
    if (setit) {
        t_filename = filename;
    } else {
        static VL_THREAD_LOCAL bool t_warned = false;
        if (VL_UNLIKELY(t_filename.empty() && !t_warned)) {
            t_warned = true;
            VL_PRINTF_MT("%%Warning: $dumpvar ignored as not proceeded by $dumpfile\n");
            return "";
        }
    }
    return t_filename.c_str();
}

//===========================================================================
// Readmem/writemem

static const char* memhFormat(int nBits) {
    assert((nBits >= 1) && (nBits <= 32));

    static VL_THREAD_LOCAL char t_buf[32];
    switch ((nBits - 1) / 4) {
    case 0: VL_SNPRINTF(t_buf, 32, "%%01x"); break;
    case 1: VL_SNPRINTF(t_buf, 32, "%%02x"); break;
    case 2: VL_SNPRINTF(t_buf, 32, "%%03x"); break;
    case 3: VL_SNPRINTF(t_buf, 32, "%%04x"); break;
    case 4: VL_SNPRINTF(t_buf, 32, "%%05x"); break;
    case 5: VL_SNPRINTF(t_buf, 32, "%%06x"); break;
    case 6: VL_SNPRINTF(t_buf, 32, "%%07x"); break;
    case 7: VL_SNPRINTF(t_buf, 32, "%%08x"); break;
    default: assert(false); break;  // LCOV_EXCL_LINE
    }
    return t_buf;
}

static const char* formatBinary(int nBits, vluint32_t bits) {
    assert((nBits >= 1) && (nBits <= 32));

    static VL_THREAD_LOCAL char t_buf[64];
    for (int i = 0; i < nBits; i++) {
        bool isOne = bits & (1 << (nBits - 1 - i));
        t_buf[i] = (isOne ? '1' : '0');
    }
    t_buf[nBits] = '\0';
    return t_buf;
}

VlReadMem::VlReadMem(bool hex, int bits, const std::string& filename, QData start, QData end)
    : m_hex{hex}
    , m_bits{bits}
    , m_filename(filename)  // Need () or GCC 4.8 false warning
    , m_end{end}
    , m_addr{start}
    , m_linenum{0} {
    m_fp = fopen(filename.c_str(), "r");
    if (VL_UNLIKELY(!m_fp)) {
        // We don't report the Verilog source filename as it slow to have to pass it down
        VL_FATAL_MT(filename.c_str(), 0, "", "$readmem file not found");
        // cppcheck-suppress resourceLeak  // m_fp is nullptr - bug in cppcheck
        return;
    }
}
VlReadMem::~VlReadMem() {
    if (m_fp) {
        fclose(m_fp);
        m_fp = nullptr;
    }
}
bool VlReadMem::get(QData& addrr, std::string& valuer) {
    if (VL_UNLIKELY(!m_fp)) return false;
    valuer = "";
    // Prep for reading
    bool indata = false;
    bool ignore_to_eol = false;
    bool ignore_to_cmt = false;
    bool reading_addr = false;
    int lastc = ' ';
    // Read the data
    // We process a character at a time, as then we don't need to deal
    // with changing buffer sizes dynamically, etc.
    while (true) {
        int c = fgetc(m_fp);
        if (VL_UNLIKELY(c == EOF)) break;
        // printf("%d: Got '%c' Addr%lx IN%d IgE%d IgC%d\n",
        //        m_linenum, c, m_addr, indata, ignore_to_eol, ignore_to_cmt);
        // See if previous data value has completed, and if so return
        if (c == '_') continue;  // Ignore _ e.g. inside a number
        if (indata && !isxdigit(c) && c != 'x' && c != 'X') {
            // printf("Got data @%lx = %s\n", m_addr, valuer.c_str());
            ungetc(c, m_fp);
            addrr = m_addr;
            ++m_addr;
            return true;
        }
        // Parse line
        if (c == '\n') {
            ++m_linenum;
            ignore_to_eol = false;
            reading_addr = false;
        } else if (c == '\t' || c == ' ' || c == '\r' || c == '\f') {
            reading_addr = false;
        }
        // Skip // comments and detect /* comments
        else if (ignore_to_cmt && lastc == '*' && c == '/') {
            ignore_to_cmt = false;
            reading_addr = false;
        } else if (!ignore_to_eol && !ignore_to_cmt) {
            if (lastc == '/' && c == '*') {
                ignore_to_cmt = true;
            } else if (lastc == '/' && c == '/') {
                ignore_to_eol = true;
            } else if (c == '/') {  // Part of /* or //
            } else if (c == '#') {
                ignore_to_eol = true;
            } else if (c == '@') {
                reading_addr = true;
                m_addr = 0;
            }
            // Check for hex or binary digits as file format requests
            else if (isxdigit(c) || (!reading_addr && (c == 'x' || c == 'X'))) {
                c = tolower(c);
                int value
                    = (c >= 'a' ? (c == 'x' ? VL_RAND_RESET_I(4) : (c - 'a' + 10)) : (c - '0'));
                if (reading_addr) {
                    // Decode @ addresses
                    m_addr = (m_addr << 4) + value;
                } else {
                    indata = true;
                    valuer += static_cast<char>(c);
                    // printf(" Value width=%d  @%x = %c\n", width, m_addr, c);
                    if (VL_UNLIKELY(value > 1 && !m_hex)) {
                        VL_FATAL_MT(m_filename.c_str(), m_linenum, "",
                                    "$readmemb (binary) file contains hex characters");
                    }
                }
            } else {
                VL_FATAL_MT(m_filename.c_str(), m_linenum, "", "$readmem file syntax error");
            }
        }
        lastc = c;
    }

    if (VL_UNLIKELY(m_end != ~0ULL && m_addr <= m_end)) {
        VL_FATAL_MT(m_filename.c_str(), m_linenum, "",
                    "$readmem file ended before specified final address (IEEE 2017 21.4)");
    }

    return false;  // EOF
}
void VlReadMem::setData(void* valuep, const std::string& rhs) {
    QData shift = m_hex ? 4ULL : 1ULL;
    bool innum = false;
    // Shift value in
    for (const auto& i : rhs) {
        char c = tolower(i);
        int value = (c >= 'a' ? (c == 'x' ? VL_RAND_RESET_I(4) : (c - 'a' + 10)) : (c - '0'));
        if (m_bits <= 8) {
            CData* datap = reinterpret_cast<CData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << shift) + value) & VL_MASK_I(m_bits);
        } else if (m_bits <= 16) {
            SData* datap = reinterpret_cast<SData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << shift) + value) & VL_MASK_I(m_bits);
        } else if (m_bits <= VL_IDATASIZE) {
            IData* datap = reinterpret_cast<IData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << shift) + value) & VL_MASK_I(m_bits);
        } else if (m_bits <= VL_QUADSIZE) {
            QData* datap = reinterpret_cast<QData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << static_cast<QData>(shift)) + static_cast<QData>(value))
                     & VL_MASK_Q(m_bits);
        } else {
            WDataOutP datap = reinterpret_cast<WDataOutP>(valuep);
            if (!innum) VL_ZERO_RESET_W(m_bits, datap);
            _VL_SHIFTL_INPLACE_W(m_bits, datap, static_cast<IData>(shift));
            datap[0] |= value;
        }
        innum = true;
    }
}

VlWriteMem::VlWriteMem(bool hex, int bits, const std::string& filename, QData start, QData end)
    : m_hex{hex}
    , m_bits{bits}
    , m_addr{0} {
    if (VL_UNLIKELY(start > end)) {
        VL_FATAL_MT(filename.c_str(), 0, "", "$writemem invalid address range");
        return;
    }

    m_fp = fopen(filename.c_str(), "w");
    if (VL_UNLIKELY(!m_fp)) {
        VL_FATAL_MT(filename.c_str(), 0, "", "$writemem file not found");
        // cppcheck-suppress resourceLeak  // m_fp is nullptr - bug in cppcheck
        return;
    }
}
VlWriteMem::~VlWriteMem() {
    if (m_fp) {
        fclose(m_fp);
        m_fp = nullptr;
    }
}
void VlWriteMem::print(QData addr, bool addrstamp, const void* valuep) {
    if (VL_UNLIKELY(!m_fp)) return;
    if (addr != m_addr && addrstamp) {  // Only assoc has time stamps
        fprintf(m_fp, "@%" VL_PRI64 "x\n", addr);
    }
    m_addr = addr + 1;
    if (m_bits <= 8) {
        const CData* datap = reinterpret_cast<const CData*>(valuep);
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits), VL_MASK_I(m_bits) & *datap);
            fprintf(m_fp, "\n");
        } else {
            fprintf(m_fp, "%s\n", formatBinary(m_bits, *datap));
        }
    } else if (m_bits <= 16) {
        const SData* datap = reinterpret_cast<const SData*>(valuep);
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits), VL_MASK_I(m_bits) & *datap);
            fprintf(m_fp, "\n");
        } else {
            fprintf(m_fp, "%s\n", formatBinary(m_bits, *datap));
        }
    } else if (m_bits <= 32) {
        const IData* datap = reinterpret_cast<const IData*>(valuep);
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits), VL_MASK_I(m_bits) & *datap);
            fprintf(m_fp, "\n");
        } else {
            fprintf(m_fp, "%s\n", formatBinary(m_bits, *datap));
        }
    } else if (m_bits <= 64) {
        const QData* datap = reinterpret_cast<const QData*>(valuep);
        vluint64_t value = VL_MASK_Q(m_bits) & *datap;
        vluint32_t lo = value & 0xffffffff;
        vluint32_t hi = value >> 32;
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits - 32), hi);
            fprintf(m_fp, "%08x\n", lo);
        } else {
            fprintf(m_fp, "%s", formatBinary(m_bits - 32, hi));
            fprintf(m_fp, "%s\n", formatBinary(32, lo));
        }
    } else {
        WDataInP datap = reinterpret_cast<WDataInP>(valuep);
        // output as a sequence of VL_EDATASIZE'd words
        // from MSB to LSB. Mask off the MSB word which could
        // contain junk above the top of valid data.
        int word_idx = ((m_bits - 1) / VL_EDATASIZE);
        bool first = true;
        while (word_idx >= 0) {
            EData data = datap[word_idx];
            if (first) {
                data &= VL_MASK_E(m_bits);
                int top_word_nbits = VL_BITBIT_E(m_bits - 1) + 1;
                if (m_hex) {
                    fprintf(m_fp, memhFormat(top_word_nbits), data);
                } else {
                    fprintf(m_fp, "%s", formatBinary(top_word_nbits, data));
                }
            } else {
                if (m_hex) {
                    fprintf(m_fp, "%08x", data);
                } else {
                    fprintf(m_fp, "%s", formatBinary(32, data));
                }
            }
            word_idx--;
            first = false;
        }
        fprintf(m_fp, "\n");
    }
}

void VL_READMEM_N(bool hex,  // Hex format, else binary
                  int bits,  // M_Bits of each array row
                  QData depth,  // Number of rows
                  int array_lsb,  // Index of first row. Valid row addresses
                  //              //  range from array_lsb up to (array_lsb + depth - 1)
                  const std::string& filename,  // Input file name
                  void* memp,  // Array state
                  QData start,  // First array row address to read
                  QData end  // Last row address to read
                  ) VL_MT_SAFE {
    if (start < static_cast<QData>(array_lsb)) start = array_lsb;

    VlReadMem rmem(hex, bits, filename, start, end);
    if (VL_UNLIKELY(!rmem.isOpen())) return;
    while (true) {
        QData addr = 0;
        std::string value;
        if (rmem.get(addr /*ref*/, value /*ref*/)) {
            if (VL_UNLIKELY(addr < static_cast<QData>(array_lsb)
                            || addr >= static_cast<QData>(array_lsb + depth))) {
                VL_FATAL_MT(filename.c_str(), rmem.linenum(), "",
                            "$readmem file address beyond bounds of array");
            } else {
                QData entry = addr - array_lsb;
                if (bits <= 8) {
                    CData* datap = &(reinterpret_cast<CData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else if (bits <= 16) {
                    SData* datap = &(reinterpret_cast<SData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else if (bits <= VL_IDATASIZE) {
                    IData* datap = &(reinterpret_cast<IData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else if (bits <= VL_QUADSIZE) {
                    QData* datap = &(reinterpret_cast<QData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else {
                    WDataOutP datap
                        = &(reinterpret_cast<WDataOutP>(memp))[entry * VL_WORDS_I(bits)];
                    rmem.setData(datap, value);
                }
            }
        } else {
            break;
        }
    }
}

void VL_WRITEMEM_N(bool hex,  // Hex format, else binary
                   int bits,  // Width of each array row
                   QData depth,  // Number of rows
                   int array_lsb,  // Index of first row. Valid row addresses
                   //              //  range from array_lsb up to (array_lsb + depth - 1)
                   const std::string& filename,  // Output file name
                   const void* memp,  // Array state
                   QData start,  // First array row address to write
                   QData end  // Last address to write, or ~0 when not specified
                   ) VL_MT_SAFE {
    QData addr_max = array_lsb + depth - 1;
    if (start < static_cast<QData>(array_lsb)) start = array_lsb;
    if (end > addr_max) end = addr_max;

    VlWriteMem wmem(hex, bits, filename, start, end);
    if (VL_UNLIKELY(!wmem.isOpen())) return;

    for (QData addr = start; addr <= end; ++addr) {
        QData row_offset = addr - array_lsb;
        if (bits <= 8) {
            const CData* datap = &(reinterpret_cast<const CData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else if (bits <= 16) {
            const SData* datap = &(reinterpret_cast<const SData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else if (bits <= 32) {
            const IData* datap = &(reinterpret_cast<const IData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else if (bits <= 64) {
            const QData* datap = &(reinterpret_cast<const QData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else {
            WDataInP memDatap = reinterpret_cast<WDataInP>(memp);
            WDataInP datap = &memDatap[row_offset * VL_WORDS_I(bits)];
            wmem.print(addr, false, datap);
        }
    }
}

//===========================================================================
// Timescale conversion

// Helper function for conversion of timescale strings
// Converts (1|10|100)(s|ms|us|ns|ps|fs) to power of then
int VL_TIME_STR_CONVERT(const char* strp) VL_PURE {
    int scale = 0;
    if (!strp) return 0;
    if (*strp++ != '1') return 0;
    while (*strp == '0') {
        scale++;
        strp++;
    }
    switch (*strp++) {
    case 's': break;
    case 'm': scale -= 3; break;
    case 'u': scale -= 6; break;
    case 'n': scale -= 9; break;
    case 'p': scale -= 12; break;
    case 'f': scale -= 15; break;
    default: return 0;
    }
    if ((scale < 0) && (*strp++ != 's')) return 0;
    if (*strp) return 0;
    return scale;
}
static const char* vl_time_str(int scale) VL_PURE {
    static const char* const names[]
        = {"100s",  "10s",  "1s",  "100ms", "10ms", "1ms", "100us", "10us", "1us",
           "100ns", "10ns", "1ns", "100ps", "10ps", "1ps", "100fs", "10fs", "1fs"};
    if (VL_UNLIKELY(scale > 2 || scale < -15)) scale = 0;
    return names[2 - scale];
}
double vl_time_multiplier(int scale) VL_PURE {
    // Return timescale multipler -18 to +18
    // For speed, this does not check for illegal values
    if (scale < 0) {
        static const double neg10[] = {1.0,
                                       0.1,
                                       0.01,
                                       0.001,
                                       0.0001,
                                       0.00001,
                                       0.000001,
                                       0.0000001,
                                       0.00000001,
                                       0.000000001,
                                       0.0000000001,
                                       0.00000000001,
                                       0.000000000001,
                                       0.0000000000001,
                                       0.00000000000001,
                                       0.000000000000001,
                                       0.0000000000000001,
                                       0.00000000000000001,
                                       0.000000000000000001};
        return neg10[-scale];
    } else {
        static const double pow10[] = {1.0,
                                       10.0,
                                       100.0,
                                       1000.0,
                                       10000.0,
                                       100000.0,
                                       1000000.0,
                                       10000000.0,
                                       100000000.0,
                                       1000000000.0,
                                       10000000000.0,
                                       100000000000.0,
                                       1000000000000.0,
                                       10000000000000.0,
                                       100000000000000.0,
                                       1000000000000000.0,
                                       10000000000000000.0,
                                       100000000000000000.0,
                                       1000000000000000000.0};
        return pow10[scale];
    }
}
const char* Verilated::timeunitString() VL_MT_SAFE { return vl_time_str(timeunit()); }
const char* Verilated::timeprecisionString() VL_MT_SAFE { return vl_time_str(timeprecision()); }

void VL_PRINTTIMESCALE(const char* namep, const char* timeunitp) VL_MT_SAFE {
    VL_PRINTF_MT("Time scale of %s is %s / %s\n", namep, timeunitp,
                 Verilated::timeprecisionString());
}
void VL_TIMEFORMAT_IINI(int units, int precision, const std::string& suffix,
                        int width) VL_MT_SAFE {
    VerilatedImp::timeFormatUnits(units);
    VerilatedImp::timeFormatPrecision(precision);
    VerilatedImp::timeFormatSuffix(suffix);
    VerilatedImp::timeFormatWidth(width);
}

//===========================================================================
// Verilated:: Methods

void Verilated::debug(int level) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_ns.s_debug = level;
    if (level) {
#ifdef VL_DEBUG
        VL_DEBUG_IF(VL_DBG_MSGF("- Verilated::debug is on."
                                " Message prefix indicates {<thread>,<sequence_number>}.\n"););
#else
        VL_PRINTF_MT("- Verilated::debug attempted,"
                     " but compiled without VL_DEBUG, so messages suppressed.\n"
                     "- Suggest remake using 'make ... CPPFLAGS=-DVL_DEBUG'\n");
#endif
    }
}
void Verilated::randReset(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_randReset = val;
}
void Verilated::randSeed(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_randSeed = val;
    vluint64_t newEpoch = s_s.s_randSeedEpoch + 1;
    if (VL_UNLIKELY(newEpoch == 0)) newEpoch = 1;
        // Obververs must see new epoch AFTER seed updated
#ifdef VL_THREADED
    std::atomic_signal_fence(std::memory_order_release);
#endif
    s_s.s_randSeedEpoch = newEpoch;
}
vluint64_t Verilated::randSeedDefault64() VL_MT_SAFE {
    if (Verilated::randSeed() != 0) {
        return ((static_cast<vluint64_t>(Verilated::randSeed()) << 32)
                ^ (static_cast<vluint64_t>(Verilated::randSeed())));
    } else {
        return ((static_cast<vluint64_t>(vl_sys_rand32()) << 32)
                ^ (static_cast<vluint64_t>(vl_sys_rand32())));
    }
}
void Verilated::calcUnusedSigs(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_calcUnusedSigs = flag;
}
void Verilated::errorCount(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_errorCount = val;
}
void Verilated::errorCountInc() VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    ++s_s.s_errorCount;
}
void Verilated::errorLimit(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_errorLimit = val;
}
void Verilated::gotFinish(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_gotFinish = flag;
}
void Verilated::assertOn(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_assertOn = flag;
}
void Verilated::fatalOnVpiError(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_fatalOnVpiError = flag;
}
void Verilated::timeunit(int value) VL_MT_SAFE {
    if (value < 0) value = -value;  // Stored as 0..15
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_timeunit = value;
}
void Verilated::timeprecision(int value) VL_MT_SAFE {
    if (value < 0) value = -value;  // Stored as 0..15
    const VerilatedLockGuard lock(s_mutex);
    s_s.s_timeprecision = value;
#ifdef SYSTEMC_VERSION
    sc_time sc_res = sc_get_time_resolution();
    int sc_prec = 99;
    if (sc_res == sc_time(1, SC_SEC)) {
        sc_prec = 0;
    } else if (sc_res == sc_time(1, SC_MS)) {
        sc_prec = 3;
    } else if (sc_res == sc_time(1, SC_US)) {
        sc_prec = 6;
    } else if (sc_res == sc_time(1, SC_NS)) {
        sc_prec = 9;
    } else if (sc_res == sc_time(1, SC_PS)) {
        sc_prec = 12;
    } else if (sc_res == sc_time(1, SC_FS)) {
        sc_prec = 15;
    }
    if (value != sc_prec) {
        std::ostringstream msg;
        msg << "SystemC's sc_set_time_resolution is 10^-" << sc_prec
            << ", which does not match Verilog timeprecision 10^-" << value
            << ". Suggest use 'sc_set_time_resolution(" << vl_time_str(value)
            << ")', or Verilator '--timescale-override " << vl_time_str(sc_prec) << "/"
            << vl_time_str(sc_prec) << "'";
        std::string msgs = msg.str();
        VL_FATAL_MT("", 0, "", msgs.c_str());
    }
#endif
}
void Verilated::profThreadsStart(vluint64_t flag) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_ns.s_profThreadsStart = flag;
}
void Verilated::profThreadsWindow(vluint64_t flag) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    s_ns.s_profThreadsWindow = flag;
}
void Verilated::profThreadsFilenamep(const char* flagp) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    if (s_ns.s_profThreadsFilenamep) free(const_cast<char*>(s_ns.s_profThreadsFilenamep));
    s_ns.s_profThreadsFilenamep = strdup(flagp);
}

const char* Verilated::catName(const char* n1, const char* n2, const char* delimiter) VL_MT_SAFE {
    // Returns new'ed data
    // Used by symbol table creation to make module names
    static VL_THREAD_LOCAL char* t_strp = nullptr;
    static VL_THREAD_LOCAL size_t t_len = 0;
    size_t newlen = strlen(n1) + strlen(n2) + strlen(delimiter) + 1;
    if (!t_strp || newlen > t_len) {
        if (t_strp) delete[] t_strp;
        t_strp = new char[newlen];
        t_len = newlen;
    }
    strcpy(t_strp, n1);
    if (*n1) strcat(t_strp, delimiter);
    strcat(t_strp, n2);
    return t_strp;
}

//=========================================================================
// Flush and exit callbacks

// Keeping these out of class Verilated to avoid having to include <list>
// in verilated.h (for compilation speed)
typedef std::list<std::pair<Verilated::VoidPCb, void*>> VoidPCbList;
static VoidPCbList s_flushCbs;
static VoidPCbList s_exitCbs;

static void addCb(Verilated::VoidPCb cb, void* datap, VoidPCbList& cbs) {
    std::pair<Verilated::VoidPCb, void*> pair(cb, datap);
    cbs.remove(pair);  // Just in case it's a duplicate
    cbs.push_back(pair);
}
static void removeCb(Verilated::VoidPCb cb, void* datap, VoidPCbList& cbs) {
    std::pair<Verilated::VoidPCb, void*> pair(cb, datap);
    cbs.remove(pair);
}
static void runCallbacks(const VoidPCbList& cbs) VL_MT_SAFE {
    for (const auto& i : cbs) i.first(i.second);
}

void Verilated::addFlushCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    addCb(cb, datap, s_flushCbs);
}
void Verilated::removeFlushCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    removeCb(cb, datap, s_flushCbs);
}
void Verilated::runFlushCallbacks() VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    runCallbacks(s_flushCbs);
    fflush(stderr);
    fflush(stdout);
    // When running internal code coverage (gcc --coverage, as opposed to
    // verilator --coverage), dump coverage data to properly cover failing
    // tests.
    VL_GCOV_FLUSH();
}

void Verilated::addExitCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    addCb(cb, datap, s_exitCbs);
}
void Verilated::removeExitCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    removeCb(cb, datap, s_exitCbs);
}
void Verilated::runExitCallbacks() VL_MT_SAFE {
    const VerilatedLockGuard lock(s_mutex);
    runCallbacks(s_exitCbs);
}

const char* Verilated::productName() VL_PURE { return VERILATOR_PRODUCT; }
const char* Verilated::productVersion() VL_PURE { return VERILATOR_VERSION; }

void Verilated::commandArgs(int argc, const char** argv) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_args.m_argMutex);
    s_args.argc = argc;
    s_args.argv = argv;
    VerilatedImp::commandArgs(argc, argv);
}

const char* Verilated::commandArgsPlusMatch(const char* prefixp) VL_MT_SAFE {
    const std::string& match = VerilatedImp::argPlusMatch(prefixp);
    static VL_THREAD_LOCAL char t_outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match.empty()) return "";
    t_outstr[0] = '\0';
    strncat(t_outstr, match.c_str(), VL_VALUE_STRING_MAX_WIDTH - 1);
    return t_outstr;
}

void Verilated::nullPointerError(const char* filename, int linenum) VL_MT_SAFE {
    // Slowpath - Called only on error
    VL_FATAL_MT(filename, linenum, "", "Null pointer dereferenced");
    VL_UNREACHABLE
}

void Verilated::overWidthError(const char* signame) VL_MT_SAFE {
    // Slowpath - Called only when signal sets too high of a bit
    std::string msg = (std::string("Testbench C set input '") + signame
                       + "' to value that overflows what the signal's width can fit");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
    VL_UNREACHABLE
}

void Verilated::mkdir(const char* dirname) VL_MT_UNSAFE {
#if defined(_WIN32) || defined(__MINGW32__)
    ::mkdir(dirname);
#else
    ::mkdir(dirname, 0777);
#endif
}

void Verilated::quiesce() VL_MT_SAFE {
#ifdef VL_THREADED
    // Wait until all threads under this evaluation are quiet
    // THREADED-TODO
#endif
}

void Verilated::internalsDump() VL_MT_SAFE { VerilatedImp::internalsDump(); }

void Verilated::scopesDump() VL_MT_SAFE { VerilatedImp::scopesDump(); }

const VerilatedScope* Verilated::scopeFind(const char* namep) VL_MT_SAFE {
    return VerilatedImp::scopeFind(namep);
}

int Verilated::exportFuncNum(const char* namep) VL_MT_SAFE {
    return VerilatedImp::exportFind(namep);
}

const VerilatedScopeNameMap* Verilated::scopeNameMap() VL_MT_SAFE {
    return VerilatedImp::scopeNameMap();
}

#ifdef VL_THREADED
void Verilated::endOfThreadMTaskGuts(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
    VL_DEBUG_IF(VL_DBG_MSGF("End of thread mtask\n"););
    VerilatedThreadMsgQueue::flush(evalMsgQp);
}

void Verilated::endOfEval(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
    // It doesn't work to set endOfEvalReqd on the threadpool thread
    // and then check it on the eval thread since it's thread local.
    // It should be ok to call into endOfEvalGuts, it returns immediately
    // if there are no transactions.
    VL_DEBUG_IF(VL_DBG_MSGF("End-of-eval cleanup\n"););
    evalMsgQp->process();
}
#endif

//===========================================================================
// VerilatedImp:: Constructors

// verilated.o may exist both in protect-lib and main module.
// Both the main module and the protect-lib refer the same instance of
// static variables such as Verilated or VerilatedImplData.
// This is important to share the state such as Verilated::gotFinish.
// But the sharing may cause double-free error when shutting down because destructors
// are called twice.
// 1st time:From protect-lib shared object on the way of unloading after exiting main()
// 2nd time:From main executable.
//
// To avoid the trouble, all member variables are enclosed in VerilatedImpU union.
// ctor nor dtor of members are not called automatically.
// VerilatedInitializer::setup() and teardown() guarantees to initialize/destruct just once.

void VerilatedImp::setup() { new (&VerilatedImp::s_s) VerilatedImpData(); }
void VerilatedImp::teardown() { VerilatedImp::s_s.~VerilatedImpU(); }

//===========================================================================
// VerilatedImp:: Methods

std::string VerilatedImp::timeFormatSuffix() VL_MT_SAFE {
    const VerilatedLockGuard lock(s_s.v.m_sergMutex);
    return s_s.v.m_serg.m_timeFormatSuffix;
}
void VerilatedImp::timeFormatSuffix(const std::string& value) VL_MT_SAFE {
    const VerilatedLockGuard lock(s_s.v.m_sergMutex);
    s_s.v.m_serg.m_timeFormatSuffix = value;
}
void VerilatedImp::timeFormatUnits(int value) VL_MT_SAFE { s_s.v.m_ser.m_timeFormatUnits = value; }
void VerilatedImp::timeFormatPrecision(int value) VL_MT_SAFE {
    s_s.v.m_ser.m_timeFormatPrecision = value;
}
void VerilatedImp::timeFormatWidth(int value) VL_MT_SAFE { s_s.v.m_ser.m_timeFormatWidth = value; }

void VerilatedImp::internalsDump() VL_MT_SAFE {
    const VerilatedLockGuard lock(s_s.v.m_argMutex);
    VL_PRINTF_MT("internalsDump:\n");
    versionDump();
    VL_PRINTF_MT("  Argv:");
    for (const auto& i : s_s.v.m_argVec) VL_PRINTF_MT(" %s", i.c_str());
    VL_PRINTF_MT("\n");
    scopesDump();
    exportsDump();
    userDump();
}
void VerilatedImp::versionDump() VL_MT_SAFE {
    VL_PRINTF_MT("  Version: %s %s\n", Verilated::productName(), Verilated::productVersion());
}

void VerilatedImp::commandArgs(int argc, const char** argv) VL_EXCLUDES(s_s.v.m_argMutex) {
    const VerilatedLockGuard lock(s_s.v.m_argMutex);
    s_s.v.m_argVec.clear();  // Always clear
    commandArgsAddGuts(argc, argv);
}
void VerilatedImp::commandArgsAdd(int argc, const char** argv) VL_EXCLUDES(s_s.v.m_argMutex) {
    const VerilatedLockGuard lock(s_s.v.m_argMutex);
    commandArgsAddGuts(argc, argv);
}
void VerilatedImp::commandArgsAddGuts(int argc, const char** argv) VL_REQUIRES(s_s.v.m_argMutex) {
    if (!s_s.v.m_argVecLoaded) s_s.v.m_argVec.clear();
    for (int i = 0; i < argc; ++i) {
        s_s.v.m_argVec.push_back(argv[i]);
        commandArgVl(argv[i]);
    }
    s_s.v.m_argVecLoaded = true;  // Can't just test later for empty vector, no arguments is ok
}
void VerilatedImp::commandArgVl(const std::string& arg) {
    if (0 == strncmp(arg.c_str(), "+verilator+", strlen("+verilator+"))) {
        std::string value;
        if (arg == "+verilator+debug") {
            Verilated::debug(4);
        } else if (commandArgVlValue(arg, "+verilator+debugi+", value /*ref*/)) {
            Verilated::debug(atoi(value.c_str()));
        } else if (commandArgVlValue(arg, "+verilator+error+limit+", value /*ref*/)) {
            Verilated::errorLimit(atoi(value.c_str()));
        } else if (arg == "+verilator+help") {
            versionDump();
            VL_PRINTF_MT("For help, please see 'verilator --help'\n");
            VL_FATAL_MT("COMMAND_LINE", 0, "",
                        "Exiting due to command line argument (not an error)");
        } else if (commandArgVlValue(arg, "+verilator+prof+threads+start+", value /*ref*/)) {
            Verilated::profThreadsStart(atoll(value.c_str()));
        } else if (commandArgVlValue(arg, "+verilator+prof+threads+window+", value /*ref*/)) {
            Verilated::profThreadsWindow(atol(value.c_str()));
        } else if (commandArgVlValue(arg, "+verilator+prof+threads+file+", value /*ref*/)) {
            Verilated::profThreadsFilenamep(value.c_str());
        } else if (commandArgVlValue(arg, "+verilator+rand+reset+", value /*ref*/)) {
            Verilated::randReset(atoi(value.c_str()));
        } else if (commandArgVlValue(arg, "+verilator+seed+", value /*ref*/)) {
            Verilated::randSeed(atoi(value.c_str()));
        } else if (arg == "+verilator+noassert") {
            Verilated::assertOn(false);
        } else if (arg == "+verilator+V") {
            versionDump();  // Someday more info too
            VL_FATAL_MT("COMMAND_LINE", 0, "",
                        "Exiting due to command line argument (not an error)");
        } else if (arg == "+verilator+version") {
            versionDump();
            VL_FATAL_MT("COMMAND_LINE", 0, "",
                        "Exiting due to command line argument (not an error)");
        } else {
            VL_PRINTF_MT("%%Warning: Unknown +verilator runtime argument: '%s'\n", arg.c_str());
        }
    }
}
bool VerilatedImp::commandArgVlValue(const std::string& arg, const std::string& prefix,
                                     std::string& valuer) {
    size_t len = prefix.length();
    if (0 == strncmp(prefix.c_str(), arg.c_str(), len)) {
        valuer = arg.substr(len);
        return true;
    } else {
        return false;
    }
}

//======================================================================
// VerilatedSyms:: Methods

VerilatedSyms::VerilatedSyms() {
#ifdef VL_THREADED
    __Vm_evalMsgQp = new VerilatedEvalMsgQueue;
#endif
}
VerilatedSyms::~VerilatedSyms() {
#ifdef VL_THREADED
    delete __Vm_evalMsgQp;
#endif
}

//===========================================================================
// VerilatedModule:: Methods

VerilatedModule::VerilatedModule(const char* namep)
    : m_namep{strdup(namep)} {}

VerilatedModule::~VerilatedModule() {
    // Memory cleanup - not called during normal operation
    // NOLINTNEXTLINE(google-readability-casting)
    if (m_namep) VL_DO_CLEAR(free((void*)(m_namep)), m_namep = nullptr);
}

//======================================================================
// VerilatedVar:: Methods

// cppcheck-suppress unusedFunction  // Used by applications
vluint32_t VerilatedVarProps::entSize() const {
    vluint32_t size = 1;
    switch (vltype()) {
    case VLVT_PTR: size = sizeof(void*); break;
    case VLVT_UINT8: size = sizeof(CData); break;
    case VLVT_UINT16: size = sizeof(SData); break;
    case VLVT_UINT32: size = sizeof(IData); break;
    case VLVT_UINT64: size = sizeof(QData); break;
    case VLVT_WDATA: size = VL_WORDS_I(packed().elements()) * sizeof(IData); break;
    default: size = 0; break;  // LCOV_EXCL_LINE
    }
    return size;
}

size_t VerilatedVarProps::totalSize() const {
    size_t size = entSize();
    for (int udim = 0; udim < udims(); ++udim) size *= m_unpacked[udim].elements();
    return size;
}

void* VerilatedVarProps::datapAdjustIndex(void* datap, int dim, int indx) const {
    if (VL_UNLIKELY(dim <= 0 || dim > udims())) return nullptr;
    if (VL_UNLIKELY(indx < low(dim) || indx > high(dim))) return nullptr;
    int indxAdj = indx - low(dim);
    vluint8_t* bytep = reinterpret_cast<vluint8_t*>(datap);
    // If on index 1 of a 2 index array, then each index 1 is index2sz*entsz
    size_t slicesz = entSize();
    for (int d = dim + 1; d <= m_udims; ++d) slicesz *= elements(d);
    bytep += indxAdj * slicesz;
    return bytep;
}

//======================================================================
// VerilatedScope:: Methods

VerilatedScope::~VerilatedScope() {
    // Memory cleanup - not called during normal operation
    VerilatedImp::scopeErase(this);
    if (m_namep) VL_DO_CLEAR(delete[] m_namep, m_namep = nullptr);
    if (m_callbacksp) VL_DO_CLEAR(delete[] m_callbacksp, m_callbacksp = nullptr);
    if (m_varsp) VL_DO_CLEAR(delete m_varsp, m_varsp = nullptr);
    m_funcnumMax = 0;  // Force callback table to empty
}

void VerilatedScope::configure(VerilatedSyms* symsp, const char* prefixp, const char* suffixp,
                               const char* identifier, vlsint8_t timeunit,
                               const Type& type) VL_MT_UNSAFE {
    // Slowpath - called once/scope at construction
    // We don't want the space and reference-count access overhead of strings.
    m_symsp = symsp;
    m_type = type;
    m_timeunit = timeunit;
    char* namep = new char[strlen(prefixp) + strlen(suffixp) + 2];
    strcpy(namep, prefixp);
    if (*prefixp && *suffixp) strcat(namep, ".");
    strcat(namep, suffixp);
    m_namep = namep;
    m_identifierp = identifier;
    VerilatedImp::scopeInsert(this);
}

void VerilatedScope::exportInsert(int finalize, const char* namep, void* cb) VL_MT_UNSAFE {
    // Slowpath - called once/scope*export at construction
    // Insert a exported function into scope table
    int funcnum = VerilatedImp::exportInsert(namep);
    if (!finalize) {
        // Need two passes so we know array size to create
        // Alternative is to dynamically stretch the array, which is more code, and slower.
        if (funcnum >= m_funcnumMax) m_funcnumMax = funcnum + 1;
    } else {
        if (VL_UNCOVERABLE(funcnum >= m_funcnumMax)) {
            VL_FATAL_MT(__FILE__, __LINE__, "",  // LCOV_EXCL_LINE
                        "Internal: Bad funcnum vs. pre-finalize maximum");
        }
        if (VL_UNLIKELY(!m_callbacksp)) {  // First allocation
            m_callbacksp = new void*[m_funcnumMax];
            memset(m_callbacksp, 0, m_funcnumMax * sizeof(void*));
        }
        m_callbacksp[funcnum] = cb;
    }
}

void VerilatedScope::varInsert(int finalize, const char* namep, void* datap, bool isParam,
                               VerilatedVarType vltype, int vlflags, int dims, ...) VL_MT_UNSAFE {
    // Grab dimensions
    // In the future we may just create a large table at emit time and
    // statically construct from that.
    if (!finalize) return;

    if (!m_varsp) m_varsp = new VerilatedVarNameMap();
    VerilatedVar var(namep, datap, vltype, static_cast<VerilatedVarFlags>(vlflags), dims, isParam);

    va_list ap;
    va_start(ap, dims);
    for (int i = 0; i < dims; ++i) {
        int msb = va_arg(ap, int);
        int lsb = va_arg(ap, int);
        if (i == 0) {
            var.m_packed.m_left = msb;
            var.m_packed.m_right = lsb;
        } else if (i >= 1 && i <= var.udims()) {
            var.m_unpacked[i - 1].m_left = msb;
            var.m_unpacked[i - 1].m_right = lsb;
        } else {
            // We could have a linked list of ranges, but really this whole thing needs
            // to be generalized to support structs and unions, etc.
            VL_FATAL_MT(
                __FILE__, __LINE__, "",
                (std::string("Unsupported multi-dimensional public varInsert: ") + namep).c_str());
        }
    }
    va_end(ap);

    m_varsp->emplace(namep, var);
}

// cppcheck-suppress unusedFunction  // Used by applications
VerilatedVar* VerilatedScope::varFind(const char* namep) const VL_MT_SAFE_POSTINIT {
    if (VL_LIKELY(m_varsp)) {
        const auto it = m_varsp->find(namep);
        if (VL_LIKELY(it != m_varsp->end())) return &(it->second);
    }
    return nullptr;
}

void* VerilatedScope::exportFindNullError(int funcnum) VL_MT_SAFE {
    // Slowpath - Called only when find has failed
    std::string msg = (std::string("Testbench C called '") + VerilatedImp::exportName(funcnum)
                       + "' but scope wasn't set, perhaps due to dpi import call without "
                       + "'context', or missing svSetScope. See IEEE 1800-2017 35.5.3.");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
    return nullptr;
}

void* VerilatedScope::exportFindError(int funcnum) const {
    // Slowpath - Called only when find has failed
    std::string msg = (std::string("Testbench C called '") + VerilatedImp::exportName(funcnum)
                       + "' but this DPI export function exists only in other scopes, not scope '"
                       + name() + "'");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
    return nullptr;
}

void VerilatedScope::scopeDump() const {
    VL_PRINTF_MT("    SCOPE %p: %s\n", this, name());
    for (int i = 0; i < m_funcnumMax; ++i) {
        if (m_callbacksp && m_callbacksp[i]) {
            VL_PRINTF_MT("       DPI-EXPORT %p: %s\n", m_callbacksp[i],
                         VerilatedImp::exportName(i));
        }
    }
    if (VerilatedVarNameMap* varsp = this->varsp()) {
        for (const auto& i : *varsp) VL_PRINTF_MT("       VAR %p: %s\n", &(i.second), i.first);
    }
}

void VerilatedHierarchy::add(VerilatedScope* fromp, VerilatedScope* top) {
    VerilatedImp::hierarchyAdd(fromp, top);
}

void VerilatedHierarchy::remove(VerilatedScope* fromp, VerilatedScope* top) {
    VerilatedImp::hierarchyRemove(fromp, top);
}

//===========================================================================
// VerilatedOneThreaded:: Methods

#if defined(VL_THREADED) && defined(VL_DEBUG)
void VerilatedAssertOneThread::fatal_different() VL_MT_SAFE {
    VL_FATAL_MT(__FILE__, __LINE__, "",
                "Routine called that is single threaded, but called from"
                " a different thread then the expected constructing thread");
}
#endif

//===========================================================================
