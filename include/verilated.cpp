// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilated general routine implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// (all code created from Verilator).
///
/// Verilator always adds this file to the Makefile for the linker.
///
/// Those macro/function/variable starting or ending in _ are internal,
/// however many of the other function/macros here are also internal.
///
//=========================================================================
// Internal note:
//
// verilated.o may exist both in --lib-create (incrementally linked .a/.so)
// and the main module.  Both refer the same instance of static
// variables/VL_THREAD_LOCAL in verilated.o such as Verilated, or
// VerilatedImpData.  This is important to share that state, but the
// sharing may cause a double-free error when shutting down because the
// loader will insert a constructor/destructor at each reference to
// verilated.o, resulting in at runtime constructors/destructors being
// called multiple times.
//
// To avoid the trouble:
//   * Statics declared inside functions. The compiler will wrap
//     the construction in must-be-one-time checks.
//   * Or, use only C++20 constinit types. (TODO: Make a VL_CONSTINIT).
//   * Or, use types that are multi-constructor safe.
//   * Or, the static should be of a union, which will avoid compiler
//     construction, and appropriately check for duplicate construction.
//   * Or, code is not linked in protected library. e.g. the VPI
//     and DPI libraries are not needed there.
//=========================================================================

#define VERILATOR_VERILATED_CPP_

#include "verilated_config.h"
#include "verilatedos.h"

#include "verilated_imp.h"

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <cstdlib>
#include <limits>
#include <list>
#include <sstream>
#include <utility>

#include <sys/stat.h>  // mkdir

// clang-format off
#if defined(_WIN32) || defined(__MINGW32__)
# include <direct.h>  // mkdir
#endif

#ifdef VL_THREADED
# include "verilated_threads.h"
#endif
// clang-format on

#include "verilated_trace.h"

// Max characters in static char string for VL_VALUE_STRING
constexpr unsigned VL_VALUE_STRING_MAX_WIDTH = 8192;

//===========================================================================
// Static sanity checks

static_assert(sizeof(uint8_t) == 1, "uint8_t is missized");
static_assert(sizeof(uint16_t) == 2, "uint8_t is missized");
static_assert(sizeof(uint32_t) == 4, "uint8_t is missized");
static_assert(sizeof(uint64_t) == 8, "uint8_t is missized");

//===========================================================================
// Global variables
// Internal note: Globals may multi-construct, see verilated.cpp top.

// Fast path, keep together
int Verilated::s_debug = 0;
VerilatedContext* Verilated::s_lastContextp = nullptr;

// Keep below together in one cache line
// Internal note: Globals may multi-construct, see verilated.cpp top.
VL_THREAD_LOCAL Verilated::ThreadLocal Verilated::t_s;

//===========================================================================
// User definable functions
// Note a TODO is a future version of the API will pass a structure so that
// the calling arguments allow for extension

#ifndef VL_USER_FINISH  ///< Define this to override the vl_finish function
void vl_finish(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    if (false && hier) {}
    VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
        "- %s:%d: Verilog $finish\n", filename, linenum);
    if (Verilated::threadContextp()->gotFinish()) {
        VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
            "- %s:%d: Second verilog $finish, exiting\n", filename, linenum);
        Verilated::runFlushCallbacks();
        Verilated::runExitCallbacks();
        std::exit(0);
    }
    Verilated::threadContextp()->gotFinish(true);
}
#endif

#ifndef VL_USER_STOP  ///< Define this to override the vl_stop function
void vl_stop(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    const char* const msg = "Verilog $stop";
    Verilated::threadContextp()->gotError(true);
    Verilated::threadContextp()->gotFinish(true);
    if (Verilated::threadContextp()->fatalOnError()) {
        vl_fatal(filename, linenum, hier, msg);
    } else {
        if (filename && filename[0]) {
            // Not VL_PRINTF_MT, already on main thread
            VL_PRINTF("%%Error: %s:%d: %s\n", filename, linenum, msg);
        } else {
            VL_PRINTF("%%Error: %s\n", msg);
        }
        Verilated::runFlushCallbacks();
    }
}
#endif

#ifndef VL_USER_FATAL  ///< Define this to override the vl_fatal function
void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_UNSAFE {
    if (false && hier) {}
    Verilated::threadContextp()->gotError(true);
    Verilated::threadContextp()->gotFinish(true);
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
    std::abort();
}
#endif

#ifndef VL_USER_STOP_MAYBE  ///< Define this to override the vl_stop_maybe function
void vl_stop_maybe(const char* filename, int linenum, const char* hier, bool maybe) VL_MT_UNSAFE {
    Verilated::threadContextp()->errorCountInc();
    if (maybe
        && Verilated::threadContextp()->errorCount() < Verilated::threadContextp()->errorLimit()) {
        VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
            "-Info: %s:%d: %s\n", filename, linenum,
            "Verilog $stop, ignored due to +verilator+error+limit");
    } else {
        vl_stop(filename, linenum, hier);
    }
}
#endif

#ifndef VL_USER_WARN  ///< Define this to override the vl_warn function
void vl_warn(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_UNSAFE {
    if (false && hier) {}
    if (filename && filename[0]) {
        // Not VL_PRINTF_MT, already on main thread
        VL_PRINTF("%%Warning: %s:%d: %s\n", filename, linenum, msg);
    } else {
        VL_PRINTF("%%Warning: %s\n", msg);
    }
    Verilated::runFlushCallbacks();
}
#endif

//===========================================================================
// Wrapper to call certain functions via messages when multithreaded

void VL_FINISH_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg{[=]() {  //
        vl_finish(filename, linenum, hier);
    }});
#else
    vl_finish(filename, linenum, hier);
#endif
}

void VL_STOP_MT(const char* filename, int linenum, const char* hier, bool maybe) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg{[=]() {  //
        vl_stop_maybe(filename, linenum, hier, maybe);
    }});
#else
    vl_stop_maybe(filename, linenum, hier, maybe);
#endif
}

void VL_FATAL_MT(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg{[=]() {  //
        vl_fatal(filename, linenum, hier, msg);
    }});
#else
    vl_fatal(filename, linenum, hier, msg);
#endif
}

void VL_WARN_MT(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg{[=]() {  //
        vl_warn(filename, linenum, hier, msg);
    }});
#else
    vl_warn(filename, linenum, hier, msg);
#endif
}

//===========================================================================
// Debug prints

// sprintf but return as string (this isn't fast, for print messages only)
std::string _vl_string_vprintf(const char* formatp, va_list ap) VL_MT_SAFE {
    va_list aq;
    va_copy(aq, ap);
    const size_t len = VL_VSNPRINTF(nullptr, 0, formatp, aq);
    va_end(aq);
    if (VL_UNLIKELY(len < 1)) return "";

    char* const bufp = new char[len + 1];
    VL_VSNPRINTF(bufp, len + 1, formatp, ap);

    std::string out{bufp, len};  // Not const to allow move optimization
    delete[] bufp;
    return out;
}

uint64_t _vl_dbg_sequence_number() VL_MT_SAFE {
#ifdef VL_THREADED
    static std::atomic<uint64_t> sequence;
#else
    static uint64_t sequence = 0;
#endif
    return ++sequence;
}

uint32_t VL_THREAD_ID() VL_MT_SAFE {
#ifdef VL_THREADED
    // Alternative is to use std::this_thread::get_id, but that returns a
    // hard-to-read number and is very slow
    static std::atomic<uint32_t> s_nextId(0);
    static VL_THREAD_LOCAL uint32_t t_myId = ++s_nextId;
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
    const std::string out = _vl_string_vprintf(formatp, ap);
    va_end(ap);
    // printf("-imm-V{t%d,%" PRId64 "}%s", VL_THREAD_ID(), _vl_dbg_sequence_number(),
    // out.c_str());

    // Using VL_PRINTF not VL_PRINTF_MT so that we can call VL_DBG_MSGF
    // from within the guts of the thread execution machinery (and it goes
    // to the screen and not into the queues we're debugging)
    VL_PRINTF("-V{t%u,%" PRIu64 "}%s", VL_THREAD_ID(), _vl_dbg_sequence_number(), out.c_str());
}

#ifdef VL_THREADED
void VL_PRINTF_MT(const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    const std::string out = _vl_string_vprintf(formatp, ap);
    va_end(ap);
    VerilatedThreadMsgQueue::post(VerilatedMsg{[=]() {  //
        VL_PRINTF("%s", out.c_str());
    }});
}
#endif

//===========================================================================
// Random -- Mostly called at init time, so not inline.

static uint32_t vl_sys_rand32() VL_MT_UNSAFE {
    // Return random 32-bits using system library.
    // Used only to construct seed for Verilator's PNRG.
    static VerilatedMutex s_mutex;
    const VerilatedLockGuard lock{s_mutex};  // Otherwise rand is unsafe
#if defined(_WIN32) && !defined(__CYGWIN__)
    // Windows doesn't have lrand48(), although Cygwin does.
    return (std::rand() << 16) ^ std::rand();
#else
    return (lrand48() << 16) ^ lrand48();
#endif
}

uint64_t vl_rand64() VL_MT_SAFE {
    static VL_THREAD_LOCAL uint64_t t_state[2];
    static VL_THREAD_LOCAL uint32_t t_seedEpoch = 0;
    // For speed, we use a thread-local epoch number to know when to reseed
    // A thread always belongs to a single context, so this works out ok
    if (VL_UNLIKELY(t_seedEpoch != VerilatedContextImp::randSeedEpoch())) {
        // Set epoch before state, to avoid race case with new seeding
        t_seedEpoch = VerilatedContextImp::randSeedEpoch();
        t_state[0] = Verilated::threadContextp()->impp()->randSeedDefault64();
        t_state[1] = t_state[0];
        // Fix state as algorithm is slow to randomize if many zeros
        // This causes a loss of ~ 1 bit of seed entropy, no big deal
        if (VL_COUNTONES_I(t_state[0]) < 10) t_state[0] = ~t_state[0];
        if (VL_COUNTONES_I(t_state[1]) < 10) t_state[1] = ~t_state[1];
    }
    // Xoroshiro128+ algorithm
    const uint64_t result = t_state[0] + t_state[1];
    t_state[1] ^= t_state[0];
    t_state[0] = (((t_state[0] << 55) | (t_state[0] >> 9)) ^ t_state[1] ^ (t_state[1] << 14));
    t_state[1] = (t_state[1] << 36) | (t_state[1] >> 28);
    return result;
}

WDataOutP VL_RANDOM_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i = 0; i < VL_WORDS_I(obits); ++i) outwp[i] = vl_rand64();
    // Last word is unclean
    return outwp;
}

IData VL_RANDOM_SEEDED_II(IData& seedr) VL_MT_SAFE {
    // $random - seed is a new seed to apply, then we return new seed
    Verilated::threadContextp()->randSeed(static_cast<int>(seedr));
    seedr = VL_RANDOM_I();
    return VL_RANDOM_I();
}
IData VL_URANDOM_SEEDED_II(IData seed) VL_MT_SAFE {
    // $urandom - seed is a new seed to apply
    Verilated::threadContextp()->randSeed(static_cast<int>(seed));
    return VL_RANDOM_I();
}
IData VL_RAND_RESET_I(int obits) VL_MT_SAFE {
    if (Verilated::threadContextp()->randReset() == 0) return 0;
    IData data = ~0;
    if (Verilated::threadContextp()->randReset() != 1) {  // if 2, randomize
        data = VL_RANDOM_I();
    }
    data &= VL_MASK_I(obits);
    return data;
}
QData VL_RAND_RESET_Q(int obits) VL_MT_SAFE {
    if (Verilated::threadContextp()->randReset() == 0) return 0;
    QData data = ~0ULL;
    if (Verilated::threadContextp()->randReset() != 1) {  // if 2, randomize
        data = VL_RANDOM_Q();
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

void _vl_debug_print_w(int lbits, const WDataInP iwp) VL_MT_SAFE {
    VL_PRINTF_MT("  Data: w%d: ", lbits);
    for (int i = VL_WORDS_I(lbits) - 1; i >= 0; --i) VL_PRINTF_MT("%08x ", iwp[i]);
    VL_PRINTF_MT("\n");
}

//===========================================================================
// Slow math

WDataOutP _vl_moddiv_w(int lbits, WDataOutP owp, const WDataInP lwp, const WDataInP rwp,
                       bool is_modulus) VL_MT_SAFE {
    // See Knuth Algorithm D.  Computes u/v = q.r
    // This isn't massively tuned, as wide division is rare
    // for debug see V3Number version
    // Requires clean input
    const int words = VL_WORDS_I(lbits);
    for (int i = 0; i < words; ++i) owp[i] = 0;
    // Find MSB and check for zero.
    const int umsbp1 = VL_MOSTSETBITP1_W(words, lwp);  // dividend
    const int vmsbp1 = VL_MOSTSETBITP1_W(words, rwp);  // divisor
    if (VL_UNLIKELY(vmsbp1 == 0)  // rwp==0 so division by zero.  Return 0.
        || VL_UNLIKELY(umsbp1 == 0)) {  // 0/x so short circuit and return 0
        return owp;
    }

    const int uw = VL_WORDS_I(umsbp1);  // aka "m" in the algorithm
    const int vw = VL_WORDS_I(vmsbp1);  // aka "n" in the algorithm

    if (vw == 1) {  // Single divisor word breaks rest of algorithm
        uint64_t k = 0;
        for (int j = uw - 1; j >= 0; --j) {
            const uint64_t unw64 = ((k << 32ULL) + static_cast<uint64_t>(lwp[j]));
            owp[j] = unw64 / static_cast<uint64_t>(rwp[0]);
            k = unw64 - static_cast<uint64_t>(owp[j]) * static_cast<uint64_t>(rwp[0]);
        }
        if (is_modulus) {
            owp[0] = k;
            for (int i = 1; i < words; ++i) owp[i] = 0;
        }
        return owp;
    }

    // +1 word as we may shift during normalization
    uint32_t un[VL_MULS_MAX_WORDS + 1];  // Fixed size, as MSVC++ doesn't allow [words] here
    uint32_t vn[VL_MULS_MAX_WORDS + 1];  // v normalized

    // Zero for ease of debugging and to save having to zero for shifts
    // Note +1 as loop will use extra word
    for (int i = 0; i < words + 1; ++i) { un[i] = vn[i] = 0; }

    // Algorithm requires divisor MSB to be set
    // Copy and shift to normalize divisor so MSB of vn[vw-1] is set
    const int s = 31 - VL_BITBIT_I(vmsbp1 - 1);  // shift amount (0...31)
    const uint32_t shift_mask = s ? 0xffffffff : 0;  // otherwise >> 32 won't mask the value
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
        const uint64_t unw64
            = (static_cast<uint64_t>(un[j + vw]) << 32ULL | static_cast<uint64_t>(un[j + vw - 1]));
        uint64_t qhat = unw64 / static_cast<uint64_t>(vn[vw - 1]);
        uint64_t rhat = unw64 - qhat * static_cast<uint64_t>(vn[vw - 1]);

    again:
        if (qhat >= 0x100000000ULL || ((qhat * vn[vw - 2]) > ((rhat << 32ULL) + un[j + vw - 2]))) {
            qhat = qhat - 1;
            rhat = rhat + vn[vw - 1];
            if (rhat < 0x100000000ULL) goto again;
        }

        int64_t t = 0;  // Must be signed
        uint64_t k = 0;
        for (int i = 0; i < vw; ++i) {
            const uint64_t p = qhat * vn[i];  // Multiply by estimate
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
                t = static_cast<uint64_t>(un[i + j]) + static_cast<uint64_t>(vn[i]) + k;
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

WDataOutP VL_POW_WWW(int obits, int, int rbits, WDataOutP owp, const WDataInP lwp,
                     const WDataInP rwp) VL_MT_SAFE {
    // obits==lbits, rbits can be different
    owp[0] = 1;
    for (int i = 1; i < VL_WORDS_I(obits); i++) owp[i] = 0;
    // cppcheck-suppress variableScope
    VlWide<VL_MULS_MAX_WORDS> powstore;  // Fixed size, as MSVC++ doesn't allow [words] here
    VlWide<VL_MULS_MAX_WORDS> lastpowstore;  // Fixed size, as MSVC++ doesn't allow [words] here
    VlWide<VL_MULS_MAX_WORDS> lastoutstore;  // Fixed size, as MSVC++ doesn't allow [words] here
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
WDataOutP VL_POW_WWQ(int obits, int lbits, int rbits, WDataOutP owp, const WDataInP lwp,
                     QData rhs) VL_MT_SAFE {
    VlWide<VL_WQ_WORDS_E> rhsw;
    VL_SET_WQ(rhsw, rhs);
    return VL_POW_WWW(obits, lbits, rbits, owp, lwp, rhsw);
}
QData VL_POW_QQW(int, int, int rbits, QData lhs, const WDataInP rwp) VL_MT_SAFE {
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

WDataOutP VL_POWSS_WWW(int obits, int, int rbits, WDataOutP owp, const WDataInP lwp,
                       const WDataInP rwp, bool lsign, bool rsign) VL_MT_SAFE {
    // obits==lbits, rbits can be different
    if (rsign && VL_SIGN_W(rbits, rwp)) {
        const int words = VL_WORDS_I(obits);
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
WDataOutP VL_POWSS_WWQ(int obits, int lbits, int rbits, WDataOutP owp, const WDataInP lwp,
                       QData rhs, bool lsign, bool rsign) VL_MT_SAFE {
    VlWide<VL_WQ_WORDS_E> rhsw;
    VL_SET_WQ(rhsw, rhs);
    return VL_POWSS_WWW(obits, lbits, rbits, owp, lwp, rhsw, lsign, rsign);
}
QData VL_POWSS_QQW(int obits, int, int rbits, QData lhs, const WDataInP rwp, bool lsign,
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

double VL_ITOR_D_W(int lbits, const WDataInP lwp) VL_PURE {
    int ms_word = VL_WORDS_I(lbits) - 1;
    for (; !lwp[ms_word] && ms_word > 0;) --ms_word;
    if (ms_word == 0) return static_cast<double>(lwp[0]);
    if (ms_word == 1) return static_cast<double>(VL_SET_QW(lwp));
    // We need 53 bits of mantissa, which might mean looking at 3 words
    // namely ms_word, ms_word-1 and ms_word-2
    const EData ihi = lwp[ms_word];
    const EData imid = lwp[ms_word - 1];
    const EData ilo = lwp[ms_word - 2];
    const double hi = static_cast<double>(ihi) * std::exp2(2 * VL_EDATASIZE);
    const double mid = static_cast<double>(imid) * std::exp2(VL_EDATASIZE);
    const double lo = static_cast<double>(ilo);
    const double d = (hi + mid + lo) * std::exp2(VL_EDATASIZE * (ms_word - 2));
    return d;
}
double VL_ISTOR_D_W(int lbits, const WDataInP lwp) VL_PURE {
    if (!VL_SIGN_W(lbits, lwp)) return VL_ITOR_D_W(lbits, lwp);
    uint32_t pos[VL_MULS_MAX_WORDS + 1];  // Fixed size, as MSVC++ doesn't allow [words] here
    VL_NEGATE_W(VL_WORDS_I(lbits), pos, lwp);
    _vl_clean_inplace_w(lbits, pos);
    return -VL_ITOR_D_W(lbits, pos);
}

//===========================================================================
// Formatting

// Output a string representation of a wide number
std::string VL_DECIMAL_NW(int width, const WDataInP lwp) VL_MT_SAFE {
    const int maxdecwidth = (width + 3) * 4 / 3;
    // Or (maxdecwidth+7)/8], but can't have more than 4 BCD bits per word
    VlWide<VL_VALUE_STRING_MAX_WIDTH / 4 + 2> bcd;
    VL_ZERO_RESET_W(maxdecwidth, bcd);
    VlWide<VL_VALUE_STRING_MAX_WIDTH / 4 + 2> tmp;
    VlWide<VL_VALUE_STRING_MAX_WIDTH / 4 + 2> tmp2;
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

template <typename T>
std::string _vl_vsformat_time(char* tmp, T ld, int timeunit, bool left, size_t width) {
    const VerilatedContextImp* const ctxImpp = Verilated::threadContextp()->impp();
    const std::string suffix = ctxImpp->timeFormatSuffix();
    const int userUnits = ctxImpp->timeFormatUnits();  // 0..-15
    const int fracDigits = ctxImpp->timeFormatPrecision();  // 0..N
    const int shift = -userUnits + fracDigits + timeunit;  // 0..-15
    int digits = 0;
    if (std::numeric_limits<T>::is_integer) {
        constexpr int b = 128;
        constexpr int w = VL_WORDS_I(b);
        VlWide<w> tmp0;
        VlWide<w> tmp1;
        VlWide<w> tmp2;
        VlWide<w> tmp3;

        WDataInP shifted = VL_EXTEND_WQ(b, 0, tmp0, static_cast<QData>(ld));
        if (shift < 0) {
            const WDataInP pow10 = VL_EXTEND_WQ(b, 0, tmp1, vl_time_pow10(-shift));
            shifted = VL_DIV_WWW(b, tmp2, shifted, pow10);
        } else {
            const WDataInP pow10 = VL_EXTEND_WQ(b, 0, tmp1, vl_time_pow10(shift));
            shifted = VL_MUL_W(w, tmp2, shifted, pow10);
        }

        const WDataInP fracDigitsPow10 = VL_EXTEND_WQ(b, 0, tmp3, vl_time_pow10(fracDigits));
        const WDataInP integer = VL_DIV_WWW(b, tmp0, shifted, fracDigitsPow10);
        const WDataInP frac = VL_MODDIV_WWW(b, tmp1, shifted, fracDigitsPow10);
        const WDataInP max64Bit
            = VL_EXTEND_WQ(b, 0, tmp2, std::numeric_limits<uint64_t>::max());  // breaks shifted
        if (VL_GT_W(w, integer, max64Bit)) {
            WDataOutP v = VL_ASSIGN_W(b, tmp3, integer);  // breaks fracDigitsPow10
            VlWide<w> zero;
            VlWide<w> ten;
            VL_ZERO_W(b, zero);
            VL_EXTEND_WI(b, 0, ten, 10);
            char buf[128];  // 128B is obviously long enough to represent 128bit integer in decimal
            char* ptr = buf + sizeof(buf) - 1;
            *ptr = '\0';
            while (VL_GT_W(w, v, zero)) {
                --ptr;
                const WDataInP mod = VL_MODDIV_WWW(b, tmp2, v, ten);  // breaks max64Bit
                *ptr = "0123456789"[VL_SET_QW(mod)];
                VlWide<w> divided;
                VL_DIV_WWW(b, divided, v, ten);
                VL_ASSIGN_W(b, v, divided);
            }
            if (!fracDigits) {
                digits = VL_SNPRINTF(tmp, VL_VALUE_STRING_MAX_WIDTH, "%s%s", ptr, suffix.c_str());
            } else {
                digits = VL_SNPRINTF(tmp, VL_VALUE_STRING_MAX_WIDTH, "%s.%0*" PRIu64 "%s", ptr,
                                     fracDigits, VL_SET_QW(frac), suffix.c_str());
            }
        } else {
            const uint64_t integer64 = VL_SET_QW(integer);
            if (!fracDigits) {
                digits = VL_SNPRINTF(tmp, VL_VALUE_STRING_MAX_WIDTH, "%" PRIu64 "%s", integer64,
                                     suffix.c_str());
            } else {
                digits = VL_SNPRINTF(tmp, VL_VALUE_STRING_MAX_WIDTH, "%" PRIu64 ".%0*" PRIu64 "%s",
                                     integer64, fracDigits, VL_SET_QW(frac), suffix.c_str());
            }
        }
    } else {
        const double shiftd = vl_time_multiplier(shift);
        const double scaled = ld * shiftd;
        const double fracDiv = vl_time_multiplier(fracDigits);
        const double whole = scaled / fracDiv;
        if (!fracDigits) {
            digits = VL_SNPRINTF(tmp, VL_VALUE_STRING_MAX_WIDTH, "%.0f%s", whole, suffix.c_str());
        } else {
            digits = VL_SNPRINTF(tmp, VL_VALUE_STRING_MAX_WIDTH, "%.*f%s", fracDigits, whole,
                                 suffix.c_str());
        }
    }

    const int needmore = width - digits;
    std::string padding;
    if (needmore > 0) padding.append(needmore, ' ');  // Pad with spaces
    return left ? (tmp + padding) : (padding + tmp);
}

// Do a va_arg returning a quad, assuming input argument is anything less than wide
#define VL_VA_ARG_Q_(ap, bits) (((bits) <= VL_IDATASIZE) ? va_arg(ap, IData) : va_arg(ap, QData))

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
            while (ep[0] && ep[0] != '%') ++ep;
            if (ep != pos) {
                output.append(pos, ep - pos);
                pos += ep - pos - 1;
            }
        } else {  // Format character
            inPct = false;
            const char fmt = pos[0];
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
                const char* const cstrp = va_arg(ap, const char*);
                if (VL_LIKELY(*cstrp)) {
                    output += cstrp;
                    output += '.';
                }
                break;
            }
            case 'S': {  // "C" string
                const char* const cstrp = va_arg(ap, const char*);
                output += cstrp;
                break;
            }
            case '@': {  // Verilog/C++ string
                va_arg(ap, int);  // # bits is ignored
                const std::string* const cstrp = va_arg(ap, const std::string*);
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
                const double d = va_arg(ap, double);
                if (lbits) {}  // UNUSED - always 64
                if (fmt == '^') {  // Realtime
                    if (!widthSet) width = Verilated::threadContextp()->impp()->timeFormatWidth();
                    const int timeunit = va_arg(ap, int);
                    output += _vl_vsformat_time(t_tmp, d, timeunit, left, width);
                } else {
                    const size_t len = pos - pctp + 1;
                    const std::string fmts{pctp, len};
                    VL_SNPRINTF(t_tmp, VL_VALUE_STRING_MAX_WIDTH, fmts.c_str(), d);
                    output += t_tmp;
                }
                break;
            }
            default: {
                // Deal with all read-and-print somethings
                const int lbits = va_arg(ap, int);
                QData ld = 0;
                VlWide<VL_WQ_WORDS_E> qlwp;
                WDataInP lwp = nullptr;
                if (lbits <= VL_QUADSIZE) {
                    ld = VL_VA_ARG_Q_(ap, lbits);
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
                    const IData charval = ld & 0xff;
                    output += static_cast<char>(charval);
                    break;
                }
                case 's': {
                    std::string field;
                    for (; lsb >= 0; --lsb) {
                        lsb = (lsb / 8) * 8;  // Next digit
                        const IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xff;
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
                        digits
                            = VL_SNPRINTF(t_tmp, VL_VALUE_STRING_MAX_WIDTH, "%" PRId64,
                                          static_cast<int64_t>(VL_EXTENDS_QQ(lbits, lbits, ld)));
                        append = t_tmp;
                    } else {
                        if (VL_SIGN_E(lbits, lwp[VL_WORDS_I(lbits) - 1])) {
                            VlWide<VL_VALUE_STRING_MAX_WIDTH / 4 + 2> neg;
                            VL_NEGATE_W(VL_WORDS_I(lbits), neg, lwp);
                            append = std::string{"-"} + VL_DECIMAL_NW(lbits, neg);
                        } else {
                            append = VL_DECIMAL_NW(lbits, lwp);
                        }
                        digits = append.length();
                    }
                    const int needmore = width - digits;
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
                        digits = VL_SNPRINTF(t_tmp, VL_VALUE_STRING_MAX_WIDTH, "%" PRIu64, ld);
                        append = t_tmp;
                    } else {
                        append = VL_DECIMAL_NW(lbits, lwp);
                        digits = append.length();
                    }
                    const int needmore = width - digits;
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
                    if (!widthSet) width = Verilated::threadContextp()->impp()->timeFormatWidth();
                    const int timeunit = va_arg(ap, int);
                    output += _vl_vsformat_time(t_tmp, ld, timeunit, left, width);
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
                        const IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xf;
                        output += "0123456789abcdef"[charval];
                    }
                    break;
                default: {  // LCOV_EXCL_START
                    const std::string msg = std::string{"Unknown _vl_vsformat code: "} + pos[0];
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
    if (VL_LIKELY(fp)) {
        return std::feof(fp) ? true : false;  // true : false to prevent MSVC++ warning
    } else {
        return floc < 0;
    }
}
static inline void _vl_vsss_advance(FILE* fp, int& floc) VL_MT_SAFE {
    if (VL_LIKELY(fp)) {
        std::fgetc(fp);
    } else {
        floc -= 8;
    }
}
static inline int _vl_vsss_peek(FILE* fp, int& floc, const WDataInP fromp,
                                const std::string& fstr) VL_MT_SAFE {
    // Get a character without advancing
    if (VL_LIKELY(fp)) {
        const int data = std::fgetc(fp);
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
static inline void _vl_vsss_skipspace(FILE* fp, int& floc, const WDataInP fromp,
                                      const std::string& fstr) VL_MT_SAFE {
    while (true) {
        const int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c == EOF || !std::isspace(c)) return;
        _vl_vsss_advance(fp, floc);
    }
}
static inline void _vl_vsss_read_str(FILE* fp, int& floc, const WDataInP fromp,
                                     const std::string& fstr, char* tmpp,
                                     const char* acceptp) VL_MT_SAFE {
    // Read into tmp, consisting of characters from acceptp list
    char* cp = tmpp;
    while (true) {
        int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c == EOF || std::isspace(c)) break;
        if (acceptp && nullptr == std::strchr(acceptp, c)) break;  // String - allow anything
        if (acceptp) c = std::tolower(c);  // Non-strings we'll simplify
        *cp++ = c;
        _vl_vsss_advance(fp, floc);
    }
    *cp++ = '\0';
    // VL_DBG_MSGF(" _read got='"<<tmpp<<"'\n");
}
static inline char* _vl_vsss_read_bin(FILE* fp, int& floc, const WDataInP fromp,
                                      const std::string& fstr, char* beginp, std::size_t n,
                                      const bool inhibit = false) {
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
    for (; nbits && lsb < obits; nbits--, lsb++, ld >>= 1) { VL_ASSIGNBIT_WI(lsb, owp, ld & 1); }
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
                  int fbits, const WDataInP fromp,  // Else if a sscanf
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
        } else if (!inPct && std::isspace(pos[0])) {  // Format spaces
            while (std::isspace(pos[1])) pos++;
            _vl_vsss_skipspace(fp, floc, fromp, fstr);
        } else if (!inPct) {  // Expected Format
            _vl_vsss_skipspace(fp, floc, fromp, fstr);
            const int c = _vl_vsss_peek(fp, floc, fromp, fstr);
            if (c != pos[0]) goto done;
            _vl_vsss_advance(fp, floc);
        } else {  // Format character
            // Skip loading spaces
            inPct = false;
            const char fmt = pos[0];
            switch (fmt) {
            case '%': {
                const int c = _vl_vsss_peek(fp, floc, fromp, fstr);
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
                VlWide<VL_WQ_WORDS_E> qowp;
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
                    const int c = _vl_vsss_peek(fp, floc, fromp, fstr);
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
                        int lpos = (static_cast<int>(std::strlen(t_tmp))) - 1;
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
                    int64_t ld = 0;
                    std::sscanf(t_tmp, "%30" PRId64, &ld);
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
                        int64_t ld;
                    } u;
                    u.r = std::strtod(t_tmp, nullptr);
                    VL_SET_WQ(owp, u.ld);
                    break;
                }
                case 't':  // FALLTHRU  // Time
                case '#': {  // Unsigned decimal
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "0123456789+-xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    QData ld = 0;
                    std::sscanf(t_tmp, "%30" PRIu64, &ld);
                    VL_SET_WQ(owp, ld);
                    break;
                }
                case 'b': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "01xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 1, t_tmp, 0, std::strlen(t_tmp));
                    break;
                }
                case 'o': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp, "01234567xXzZ?_");
                    if (!t_tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 3, t_tmp, 0, std::strlen(t_tmp));
                    break;
                }
                case 'x': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read_str(fp, floc, fromp, fstr, t_tmp,
                                      "0123456789abcdefABCDEFxXzZ?_");
                    if (!t_tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 4, t_tmp, 0, std::strlen(t_tmp));
                    break;
                }
                case 'u': {
                    // Read packed 2-value binary data
                    const int bytes = VL_BYTES_I(obits);
                    char* const out = reinterpret_cast<char*>(owp);
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
                    const std::string msg = std::string{"Unknown _vl_vsscanf code: "} + pos[0];
                    VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
                    break;
                }  // LCOV_EXCL_STOP

                }  // switch

                if (!inIgnore) ++got;
                // Reload data if non-wide (if wide, we put it in the right place directly)
                if (obits == 0) {  // Due to inIgnore
                } else if (obits == -1) {  // string
                    std::string* const p = va_arg(ap, std::string*);
                    *p = t_tmp;
                } else if (obits <= VL_BYTESIZE) {
                    CData* const p = va_arg(ap, CData*);
                    *p = owp[0];
                } else if (obits <= VL_SHORTSIZE) {
                    SData* const p = va_arg(ap, SData*);
                    *p = owp[0];
                } else if (obits <= VL_IDATASIZE) {
                    IData* const p = va_arg(ap, IData*);
                    *p = owp[0];
                } else if (obits <= VL_QUADSIZE) {
                    QData* const p = va_arg(ap, QData*);
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
    return Verilated::threadContextp()->impp()->fdToFp(lhs);
}

void _vl_vint_to_string(int obits, char* destoutp, const WDataInP sourcep) VL_MT_SAFE {
    // See also VL_DATA_TO_STRING_NW
    int lsb = obits - 1;
    bool start = true;
    char* destp = destoutp;
    for (; lsb >= 0; --lsb) {
        lsb = (lsb / 8) * 8;  // Next digit
        const IData charval = VL_BITRSHIFT_W(sourcep, lsb) & 0xff;
        if (!start || charval) {
            *destp++ = (charval == 0) ? ' ' : charval;
            start = false;  // Drop leading 0s
        }
    }
    *destp = '\0';  // Terminate
    if (!start) {  // Drop trailing spaces
        while (std::isspace(*(destp - 1)) && destp > destoutp) *--destp = '\0';
    }
}

void _vl_string_to_vint(int obits, void* destp, size_t srclen, const char* srcp) VL_MT_SAFE {
    // Convert C string to Verilog format
    const size_t bytes = VL_BYTES_I(obits);
    char* op = reinterpret_cast<char*>(destp);
    if (srclen > bytes) srclen = bytes;  // Don't overflow destination
    size_t i = 0;
    for (i = 0; i < srclen; ++i) { *op++ = srcp[srclen - 1 - i]; }
    for (; i < bytes; ++i) { *op++ = 0; }
}

static IData getLine(std::string& str, IData fpi, size_t maxLen) VL_MT_SAFE {
    str.clear();

    // While threadsafe, each thread can only access different file handles
    FILE* const fp = VL_CVT_I_FP(fpi);
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
    const IData got = getLine(str, fpi, bytes);

    if (VL_UNLIKELY(str.empty())) return 0;

    // V3Emit has static check that bytes < VL_VALUE_STRING_MAX_WORDS, but be safe
    if (VL_UNCOVERABLE(bytes < str.size())) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: fgets buffer overrun");  // LCOV_EXCL_LINE
    }

    _vl_string_to_vint(obits, destp, got, str.data());
    return got;
}

IData VL_FGETS_NI(std::string& dest, IData fpi) VL_MT_SAFE {
    return getLine(dest, fpi, std::numeric_limits<size_t>::max());
}

IData VL_FERROR_IN(IData, std::string& outputr) VL_MT_SAFE {
    // We ignore lhs/fpi - IEEE says "most recent error" so probably good enough
    const IData ret = errno;
    outputr = std::string{::std::strerror(ret)};
    return ret;
}

IData VL_FOPEN_NN(const std::string& filename, const std::string& mode) {
    return Verilated::threadContextp()->impp()->fdNew(filename.c_str(), mode.c_str());
}
IData VL_FOPEN_MCD_N(const std::string& filename) VL_MT_SAFE {
    return Verilated::threadContextp()->impp()->fdNewMcd(filename.c_str());
}

void VL_FFLUSH_I(IData fdi) VL_MT_SAFE { Verilated::threadContextp()->impp()->fdFlush(fdi); }
IData VL_FSEEK_I(IData fdi, IData offset, IData origin) VL_MT_SAFE {
    return Verilated::threadContextp()->impp()->fdSeek(fdi, offset, origin);
}
IData VL_FTELL_I(IData fdi) VL_MT_SAFE { return Verilated::threadContextp()->impp()->fdTell(fdi); }
void VL_FCLOSE_I(IData fdi) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    Verilated::threadContextp()->impp()->fdClose(fdi);
}

void VL_SFORMAT_X(int obits, CData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _vl_string_to_vint(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, SData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _vl_string_to_vint(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, IData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _vl_string_to_vint(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, QData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _vl_string_to_vint(obits, &destr, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits, void* destp, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string t_output;  // static only for speed
    t_output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(t_output, formatp, ap);
    va_end(ap);

    _vl_string_to_vint(obits, destp, t_output.length(), t_output.c_str());
}

void VL_SFORMAT_X(int obits_ignored, std::string& output, const char* formatp, ...) VL_MT_SAFE {
    if (obits_ignored) {}
    std::string temp_output;
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(temp_output, formatp, ap);
    va_end(ap);
    output = temp_output;
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

    Verilated::threadContextp()->impp()->fdWrite(fpi, t_output);
}

IData VL_FSCANF_IX(IData fpi, const char* formatp, ...) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* const fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return ~0U;  // -1

    va_list ap;
    va_start(ap, formatp);
    const IData got = _vl_vsscanf(fp, 0, nullptr, "", formatp, ap);
    va_end(ap);
    return got;
}

IData VL_SSCANF_IIX(int lbits, IData ld, const char* formatp, ...) VL_MT_SAFE {
    VlWide<VL_WQ_WORDS_E> fnw;
    VL_SET_WI(fnw, ld);

    va_list ap;
    va_start(ap, formatp);
    const IData got = _vl_vsscanf(nullptr, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IQX(int lbits, QData ld, const char* formatp, ...) VL_MT_SAFE {
    VlWide<VL_WQ_WORDS_E> fnw;
    VL_SET_WQ(fnw, ld);

    va_list ap;
    va_start(ap, formatp);
    const IData got = _vl_vsscanf(nullptr, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IWX(int lbits, const WDataInP lwp, const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    const IData got = _vl_vsscanf(nullptr, lbits, lwp, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_INX(int, const std::string& ld, const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    const IData got = _vl_vsscanf(nullptr, ld.length() * 8, nullptr, ld, formatp, ap);
    va_end(ap);
    return got;
}

IData VL_FREAD_I(int width, int array_lsb, int array_size, void* memp, IData fpi, IData start,
                 IData count) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* const fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;
    if (count > (array_size - (start - array_lsb))) count = array_size - (start - array_lsb);
    // Prep for reading
    IData read_count = 0;
    IData read_elements = 0;
    const int start_shift = (width - 1) & ~7;  // bit+7:bit gets first character
    int shift = start_shift;
    // Read the data
    // We process a character at a time, as then we don't need to deal
    // with changing buffer sizes dynamically, etc.
    while (true) {
        const int c = std::fgetc(fp);
        if (VL_UNLIKELY(c == EOF)) break;
        // Shift value in
        const IData entry = read_elements + start - array_lsb;
        if (width <= 8) {
            CData* const datap = &(reinterpret_cast<CData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= 16) {
            SData* const datap = &(reinterpret_cast<SData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= VL_IDATASIZE) {
            IData* const datap = &(reinterpret_cast<IData*>(memp))[entry];
            if (shift == start_shift) *datap = 0;
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= VL_QUADSIZE) {
            QData* const datap = &(reinterpret_cast<QData*>(memp))[entry];
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
    VlWide<VL_WQ_WORDS_E> lhsw;
    VL_SET_WQ(lhsw, lhs);
    return VL_SYSTEM_IW(VL_WQ_WORDS_E, lhsw);
}
IData VL_SYSTEM_IW(int lhswords, const WDataInP lhsp) VL_MT_SAFE {
    char filenamez[VL_VALUE_STRING_MAX_CHARS + 1];
    _vl_vint_to_string(lhswords * VL_EDATASIZE, filenamez, lhsp);
    const int code = std::system(filenamez);  // Yes, std::system() is threadsafe
    return code >> 8;  // Want exit status
}

IData VL_TESTPLUSARGS_I(const std::string& format) VL_MT_SAFE {
    const std::string& match = Verilated::threadContextp()->impp()->argPlusMatch(format.c_str());
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
        } else if (inPct && posp[0] == '0') {  // %0
        } else {  // Format character
            switch (std::tolower(*posp)) {
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

    const std::string& match = Verilated::threadContextp()->impp()->argPlusMatch(prefix.c_str());
    const char* const dp = match.c_str() + 1 /*leading + */ + prefix.length();
    if (match.empty()) return 0;

    VL_ZERO_RESET_W(rbits, rwp);
    switch (std::tolower(fmt)) {
    case 'd': {
        int64_t lld = 0;
        std::sscanf(dp, "%30" PRId64, &lld);
        VL_SET_WQ(rwp, lld);
        break;
    }
    case 'b': _vl_vsss_based(rwp, rbits, 1, dp, 0, std::strlen(dp)); break;
    case 'o': _vl_vsss_based(rwp, rbits, 3, dp, 0, std::strlen(dp)); break;
    case 'h':  // FALLTHRU
    case 'x': _vl_vsss_based(rwp, rbits, 4, dp, 0, std::strlen(dp)); break;
    case 's': {  // string/no conversion
        for (int i = 0, lsb = 0, posp = static_cast<int>(std::strlen(dp)) - 1;
             i < rbits && posp >= 0; --posp) {
            _vl_vsss_setbit(rwp, rbits, lsb, 8, dp[posp]);
            lsb += 8;
        }
        break;
    }
    case 'e': {
        double temp = 0.F;
        std::sscanf(dp, "%le", &temp);
        VL_SET_WQ(rwp, VL_CVT_Q_D(temp));
        break;
    }
    case 'f': {
        double temp = 0.F;
        std::sscanf(dp, "%lf", &temp);
        VL_SET_WQ(rwp, VL_CVT_Q_D(temp));
        break;
    }
    case 'g': {
        double temp = 0.F;
        std::sscanf(dp, "%lg", &temp);
        VL_SET_WQ(rwp, VL_CVT_Q_D(temp));
        break;
    }
    default:  // Other simulators return 0 in these cases and don't error out
        return 0;
    }
    _vl_clean_inplace_w(rbits, rwp);
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
            switch (std::tolower(*posp)) {
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
    const std::string& match = Verilated::threadContextp()->impp()->argPlusMatch(prefix.c_str());
    const char* const dp = match.c_str() + 1 /*leading + */ + prefix.length();
    if (match.empty()) return 0;
    rdr = std::string{dp};
    return 1;
}

const char* vl_mc_scan_plusargs(const char* prefixp) VL_MT_SAFE {
    const std::string& match = Verilated::threadContextp()->impp()->argPlusMatch(prefixp);
    static VL_THREAD_LOCAL char t_outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match.empty()) return nullptr;
    char* dp = t_outstr;
    for (const char* sp = match.c_str() + std::strlen(prefixp) + 1;  // +1 to skip the "+"
         *sp && (dp - t_outstr) < (VL_VALUE_STRING_MAX_WIDTH - 2);)
        *dp++ = *sp++;
    *dp++ = '\0';
    return t_outstr;
}

//===========================================================================
// Heavy string functions

std::string VL_TO_STRING(CData lhs) { return VL_SFORMATF_NX("'h%0x", 8, lhs); }
std::string VL_TO_STRING(SData lhs) { return VL_SFORMATF_NX("'h%0x", 16, lhs); }
std::string VL_TO_STRING(IData lhs) { return VL_SFORMATF_NX("'h%0x", 32, lhs); }
std::string VL_TO_STRING(QData lhs) { return VL_SFORMATF_NX("'h%0x", 64, lhs); }
std::string VL_TO_STRING_W(int words, const WDataInP obj) {
    return VL_SFORMATF_NX("'h%0x", words * VL_EDATASIZE, obj);
}

std::string VL_TOLOWER_NN(const std::string& ld) VL_MT_SAFE {
    std::string out = ld;
    for (auto& cr : out) cr = std::tolower(cr);
    return out;
}
std::string VL_TOUPPER_NN(const std::string& ld) VL_MT_SAFE {
    std::string out = ld;
    for (auto& cr : out) cr = std::toupper(cr);
    return out;
}

std::string VL_CVT_PACK_STR_NW(int lwords, const WDataInP lwp) VL_MT_SAFE {
    // See also _vl_vint_to_string
    char destout[VL_VALUE_STRING_MAX_CHARS + 1];
    const int obits = lwords * VL_EDATASIZE;
    int lsb = obits - 1;
    bool start = true;
    char* destp = destout;
    size_t len = 0;
    for (; lsb >= 0; --lsb) {
        lsb = (lsb / 8) * 8;  // Next digit
        const IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xff;
        if (!start || charval) {
            *destp++ = (charval == 0) ? ' ' : charval;
            ++len;
            start = false;  // Drop leading 0s
        }
    }
    return std::string{destout, len};
}

std::string VL_PUTC_N(const std::string& lhs, IData rhs, CData ths) VL_PURE {
    std::string lstring = lhs;
    const int32_t rhs_s = rhs;  // To signed value
    // 6.16.2:str.putc(i, c) does not change the value when i < 0 || i >= str.len() || c == 0
    if (0 <= rhs_s && rhs < lhs.length() && ths != 0) lstring[rhs] = ths;
    return lstring;
}

CData VL_GETC_N(const std::string& lhs, IData rhs) VL_PURE {
    CData v = 0;
    const int32_t rhs_s = rhs;  // To signed value
    // 6.16.3:str.getc(i) returns 0 if i < 0 || i >= str.len()
    if (0 <= rhs_s && rhs < lhs.length()) v = lhs[rhs];
    return v;
}

std::string VL_SUBSTR_N(const std::string& lhs, IData rhs, IData ths) VL_PURE {
    const int32_t rhs_s = rhs;  // To signed value
    const int32_t ths_s = ths;  // To signed value
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

static const char* formatBinary(int nBits, uint32_t bits) {
    assert((nBits >= 1) && (nBits <= 32));

    static VL_THREAD_LOCAL char t_buf[64];
    for (int i = 0; i < nBits; i++) {
        const bool isOne = bits & (1 << (nBits - 1 - i));
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
    , m_addr{start} {
    m_fp = std::fopen(filename.c_str(), "r");
    if (VL_UNLIKELY(!m_fp)) {
        // We don't report the Verilog source filename as it slow to have to pass it down
        VL_WARN_MT(filename.c_str(), 0, "", "$readmem file not found");
        // cppcheck-suppress resourceLeak  // m_fp is nullptr - bug in cppcheck
        return;
    }
}
VlReadMem::~VlReadMem() {
    if (m_fp) {
        std::fclose(m_fp);
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
        int c = std::fgetc(m_fp);
        if (VL_UNLIKELY(c == EOF)) break;
        // printf("%d: Got '%c' Addr%lx IN%d IgE%d IgC%d\n",
        //        m_linenum, c, m_addr, indata, ignore_to_eol, ignore_to_cmt);
        // See if previous data value has completed, and if so return
        if (c == '_') continue;  // Ignore _ e.g. inside a number
        if (indata && !std::isxdigit(c) && c != 'x' && c != 'X') {
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
                m_anyAddr = true;
                m_addr = 0;
            }
            // Check for hex or binary digits as file format requests
            else if (std::isxdigit(c) || (!reading_addr && (c == 'x' || c == 'X'))) {
                c = std::tolower(c);
                const int value
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

    if (VL_UNLIKELY(m_end != ~0ULL && m_addr <= m_end && !m_anyAddr)) {
        VL_WARN_MT(m_filename.c_str(), m_linenum, "",
                   "$readmem file ended before specified final address (IEEE 2017 21.4)");
    }

    return false;  // EOF
}
void VlReadMem::setData(void* valuep, const std::string& rhs) {
    const QData shift = m_hex ? 4ULL : 1ULL;
    bool innum = false;
    // Shift value in
    for (const auto& i : rhs) {
        const char c = std::tolower(i);
        const int value
            = (c >= 'a' ? (c == 'x' ? VL_RAND_RESET_I(4) : (c - 'a' + 10)) : (c - '0'));
        if (m_bits <= 8) {
            CData* const datap = reinterpret_cast<CData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << shift) + value) & VL_MASK_I(m_bits);
        } else if (m_bits <= 16) {
            SData* const datap = reinterpret_cast<SData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << shift) + value) & VL_MASK_I(m_bits);
        } else if (m_bits <= VL_IDATASIZE) {
            IData* const datap = reinterpret_cast<IData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << shift) + value) & VL_MASK_I(m_bits);
        } else if (m_bits <= VL_QUADSIZE) {
            QData* const datap = reinterpret_cast<QData*>(valuep);
            if (!innum) *datap = 0;
            *datap = ((*datap << static_cast<QData>(shift)) + static_cast<QData>(value))
                     & VL_MASK_Q(m_bits);
        } else {
            WDataOutP datap = reinterpret_cast<WDataOutP>(valuep);
            if (!innum) VL_ZERO_RESET_W(m_bits, datap);
            _vl_shiftl_inplace_w(m_bits, datap, static_cast<IData>(shift));
            datap[0] |= value;
        }
        innum = true;
    }
}

VlWriteMem::VlWriteMem(bool hex, int bits, const std::string& filename, QData start, QData end)
    : m_hex{hex}
    , m_bits{bits} {
    if (VL_UNLIKELY(start > end)) {
        VL_FATAL_MT(filename.c_str(), 0, "", "$writemem invalid address range");
        return;
    }

    m_fp = std::fopen(filename.c_str(), "w");
    if (VL_UNLIKELY(!m_fp)) {
        VL_FATAL_MT(filename.c_str(), 0, "", "$writemem file not found");
        // cppcheck-suppress resourceLeak  // m_fp is nullptr - bug in cppcheck
        return;
    }
}
VlWriteMem::~VlWriteMem() {
    if (m_fp) {
        std::fclose(m_fp);
        m_fp = nullptr;
    }
}
void VlWriteMem::print(QData addr, bool addrstamp, const void* valuep) {
    if (VL_UNLIKELY(!m_fp)) return;
    if (addr != m_addr && addrstamp) {  // Only assoc has time stamps
        fprintf(m_fp, "@%" PRIx64 "\n", addr);
    }
    m_addr = addr + 1;
    if (m_bits <= 8) {
        const CData* const datap = reinterpret_cast<const CData*>(valuep);
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits), VL_MASK_I(m_bits) & *datap);
            fprintf(m_fp, "\n");
        } else {
            fprintf(m_fp, "%s\n", formatBinary(m_bits, *datap));
        }
    } else if (m_bits <= 16) {
        const SData* const datap = reinterpret_cast<const SData*>(valuep);
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits), VL_MASK_I(m_bits) & *datap);
            fprintf(m_fp, "\n");
        } else {
            fprintf(m_fp, "%s\n", formatBinary(m_bits, *datap));
        }
    } else if (m_bits <= 32) {
        const IData* const datap = reinterpret_cast<const IData*>(valuep);
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits), VL_MASK_I(m_bits) & *datap);
            fprintf(m_fp, "\n");
        } else {
            fprintf(m_fp, "%s\n", formatBinary(m_bits, *datap));
        }
    } else if (m_bits <= 64) {
        const QData* const datap = reinterpret_cast<const QData*>(valuep);
        const uint64_t value = VL_MASK_Q(m_bits) & *datap;
        const uint32_t lo = value & 0xffffffff;
        const uint32_t hi = value >> 32;
        if (m_hex) {
            fprintf(m_fp, memhFormat(m_bits - 32), hi);
            fprintf(m_fp, "%08x\n", lo);
        } else {
            fprintf(m_fp, "%s", formatBinary(m_bits - 32, hi));
            fprintf(m_fp, "%s\n", formatBinary(32, lo));
        }
    } else {
        const WDataInP datap = reinterpret_cast<WDataInP>(valuep);
        // output as a sequence of VL_EDATASIZE'd words
        // from MSB to LSB. Mask off the MSB word which could
        // contain junk above the top of valid data.
        int word_idx = ((m_bits - 1) / VL_EDATASIZE);
        bool first = true;
        while (word_idx >= 0) {
            EData data = datap[word_idx];
            if (first) {
                data &= VL_MASK_E(m_bits);
                const int top_word_nbits = VL_BITBIT_E(m_bits - 1) + 1;
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
            --word_idx;
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

    VlReadMem rmem{hex, bits, filename, start, end};
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
                const QData entry = addr - array_lsb;
                if (bits <= 8) {
                    CData* const datap = &(reinterpret_cast<CData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else if (bits <= 16) {
                    SData* const datap = &(reinterpret_cast<SData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else if (bits <= VL_IDATASIZE) {
                    IData* const datap = &(reinterpret_cast<IData*>(memp))[entry];
                    rmem.setData(datap, value);
                } else if (bits <= VL_QUADSIZE) {
                    QData* const datap = &(reinterpret_cast<QData*>(memp))[entry];
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
    const QData addr_max = array_lsb + depth - 1;
    if (start < static_cast<QData>(array_lsb)) start = array_lsb;
    if (end > addr_max) end = addr_max;

    VlWriteMem wmem{hex, bits, filename, start, end};
    if (VL_UNLIKELY(!wmem.isOpen())) return;

    for (QData addr = start; addr <= end; ++addr) {
        const QData row_offset = addr - array_lsb;
        if (bits <= 8) {
            const CData* const datap = &(reinterpret_cast<const CData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else if (bits <= 16) {
            const SData* const datap = &(reinterpret_cast<const SData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else if (bits <= 32) {
            const IData* const datap = &(reinterpret_cast<const IData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else if (bits <= 64) {
            const QData* const datap = &(reinterpret_cast<const QData*>(memp))[row_offset];
            wmem.print(addr, false, datap);
        } else {
            const WDataInP memDatap = reinterpret_cast<WDataInP>(memp);
            const WDataInP datap = &memDatap[row_offset * VL_WORDS_I(bits)];
            wmem.print(addr, false, datap);
        }
    }
}

//===========================================================================
// Timescale conversion

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
uint64_t vl_time_pow10(int n) {
    static const uint64_t pow10[20] = {
        1ULL,
        10ULL,
        100ULL,
        1000ULL,
        10000ULL,
        100000ULL,
        1000000ULL,
        10000000ULL,
        100000000ULL,
        1000000000ULL,
        10000000000ULL,
        100000000000ULL,
        1000000000000ULL,
        10000000000000ULL,
        100000000000000ULL,
        1000000000000000ULL,
        10000000000000000ULL,
        100000000000000000ULL,
        1000000000000000000ULL,
    };
    return pow10[n];
}

void VL_PRINTTIMESCALE(const char* namep, const char* timeunitp,
                       const VerilatedContext* contextp) VL_MT_SAFE {
    VL_PRINTF_MT("Time scale of %s is %s / %s\n", namep, timeunitp,
                 contextp->timeprecisionString());
}
void VL_TIMEFORMAT_IINI(int units, int precision, const std::string& suffix, int width,
                        VerilatedContext* contextp) VL_MT_SAFE {
    contextp->impp()->timeFormatUnits(units);
    contextp->impp()->timeFormatPrecision(precision);
    contextp->impp()->timeFormatSuffix(suffix);
    contextp->impp()->timeFormatWidth(width);
}

//======================================================================
// VerilatedContext:: Methods

VerilatedContext::VerilatedContext()
    : m_impdatap{new VerilatedContextImpData} {
    Verilated::lastContextp(this);
    Verilated::threadContextp(this);
    m_ns.m_profExecFilename = "profile_exec.dat";
    m_ns.m_profVltFilename = "profile.vlt";
    m_fdps.resize(31);
    std::fill(m_fdps.begin(), m_fdps.end(), static_cast<FILE*>(nullptr));
    m_fdFreeMct.resize(30);
    for (std::size_t i = 0, id = 1; i < m_fdFreeMct.size(); ++i, ++id) m_fdFreeMct[i] = id;
}

// Must declare here not in interface, as otherwise forward declarations not known
VerilatedContext::~VerilatedContext() {
    checkMagic(this);
    m_magic = 0x1;  // Arbitrary but 0x1 is what Verilator src uses for a deleted pointer
}

void VerilatedContext::checkMagic(const VerilatedContext* contextp) {
    if (VL_UNLIKELY(!contextp || contextp->m_magic != MAGIC)) {
        VL_FATAL_MT("", 0, "",  // LCOV_EXCL_LINE
                    "Attempt to create model using a bad/deleted VerilatedContext pointer");
    }
}

VerilatedContext::Serialized::Serialized() {
    constexpr int8_t picosecond = -12;
    m_timeunit = picosecond;  // Initial value until overriden by _Vconfigure
    m_timeprecision = picosecond;  // Initial value until overriden by _Vconfigure
}

void VerilatedContext::assertOn(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_assertOn = flag;
}
void VerilatedContext::calcUnusedSigs(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_calcUnusedSigs = flag;
}
void VerilatedContext::dumpfile(const std::string& flag) VL_MT_SAFE_EXCLUDES(m_timeDumpMutex) {
    const VerilatedLockGuard lock{m_timeDumpMutex};
    m_dumpfile = flag;
}
std::string VerilatedContext::dumpfile() const VL_MT_SAFE_EXCLUDES(m_timeDumpMutex) {
    const VerilatedLockGuard lock{m_timeDumpMutex};
    return m_dumpfile;
}
std::string VerilatedContext::dumpfileCheck() const VL_MT_SAFE_EXCLUDES(m_timeDumpMutex) {
    std::string out = dumpfile();
    if (VL_UNLIKELY(out.empty())) {
        VL_PRINTF_MT("%%Warning: $dumpvar ignored as not proceeded by $dumpfile\n");
        return "";
    }
    return out;
}
void VerilatedContext::errorCount(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_errorCount = val;
}
void VerilatedContext::errorCountInc() VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    ++m_s.m_errorCount;
}
void VerilatedContext::errorLimit(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_errorLimit = val;
}
void VerilatedContext::fatalOnError(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_fatalOnError = flag;
}
void VerilatedContext::fatalOnVpiError(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_fatalOnVpiError = flag;
}
void VerilatedContext::gotError(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_gotError = flag;
}
void VerilatedContext::gotFinish(bool flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_gotFinish = flag;
}
void VerilatedContext::profExecStart(uint64_t flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_ns.m_profExecStart = flag;
}
void VerilatedContext::profExecWindow(uint64_t flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_ns.m_profExecWindow = flag;
}
void VerilatedContext::profExecFilename(const std::string& flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_ns.m_profExecFilename = flag;
}
std::string VerilatedContext::profExecFilename() const VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    return m_ns.m_profExecFilename;
}
void VerilatedContext::profVltFilename(const std::string& flag) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_ns.m_profVltFilename = flag;
}
std::string VerilatedContext::profVltFilename() const VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    return m_ns.m_profVltFilename;
}
void VerilatedContext::randReset(int val) VL_MT_SAFE {
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_randReset = val;
}
void VerilatedContext::timeunit(int value) VL_MT_SAFE {
    if (value < 0) value = -value;  // Stored as 0..15
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_timeunit = value;
}
void VerilatedContext::timeprecision(int value) VL_MT_SAFE {
    if (value < 0) value = -value;  // Stored as 0..15
    const VerilatedLockGuard lock{m_mutex};
    m_s.m_timeprecision = value;
#ifdef SYSTEMC_VERSION
    const sc_time sc_res = sc_get_time_resolution();
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
        const std::string msgs = msg.str();
        VL_FATAL_MT("", 0, "", msgs.c_str());
    }
#endif
}
const char* VerilatedContext::timeunitString() const VL_MT_SAFE { return vl_time_str(timeunit()); }
const char* VerilatedContext::timeprecisionString() const VL_MT_SAFE {
    return vl_time_str(timeprecision());
}

void VerilatedContext::threads(unsigned n) {
    if (n == 0) VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: Simulation threads must be >= 1");

    if (m_threadPool) {
        VL_FATAL_MT(
            __FILE__, __LINE__, "",
            "%Error: Cannot set simulation threads after the thread pool has been created.");
    }

#if VL_THREADED
    if (m_threads == n) return;  // To avoid unnecessary warnings
    m_threads = n;
    const unsigned hardwareThreadsAvailable = std::thread::hardware_concurrency();
    if (m_threads > hardwareThreadsAvailable) {
        VL_PRINTF_MT("%%Warning: System has %u hardware threads but simulation thread count set "
                     "to %u. This will likely cause significant slowdown.\n",
                     hardwareThreadsAvailable, m_threads);
    }
#else
    if (n > 1) {
        VL_PRINTF_MT("%%Warning: Verilator run-time library built without VL_THREADS. Ignoring "
                     "call to 'VerilatedContext::threads' with argument %u.\n",
                     n);
    }
#endif
}

void VerilatedContext::commandArgs(int argc, const char** argv) VL_MT_SAFE_EXCLUDES(m_argMutex) {
    const VerilatedLockGuard lock{m_argMutex};
    m_args.m_argVec.clear();  // Empty first, then add
    impp()->commandArgsAddGuts(argc, argv);
}
void VerilatedContext::commandArgsAdd(int argc, const char** argv)
    VL_MT_SAFE_EXCLUDES(m_argMutex) {
    const VerilatedLockGuard lock{m_argMutex};
    impp()->commandArgsAddGuts(argc, argv);
}
const char* VerilatedContext::commandArgsPlusMatch(const char* prefixp)
    VL_MT_SAFE_EXCLUDES(m_argMutex) {
    const std::string& match = impp()->argPlusMatch(prefixp);
    static VL_THREAD_LOCAL char t_outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match.empty()) return "";
    char* dp = t_outstr;
    for (const char* sp = match.c_str(); *sp && (dp - t_outstr) < (VL_VALUE_STRING_MAX_WIDTH - 2);)
        *dp++ = *sp++;
    *dp++ = '\0';
    return t_outstr;
}
void VerilatedContext::internalsDump() const VL_MT_SAFE {
    VL_PRINTF_MT("internalsDump:\n");
    VerilatedImp::versionDump();
    impp()->commandArgDump();
    impp()->scopesDump();
    VerilatedImp::exportsDump();
    VerilatedImp::userDump();
}

void VerilatedContext::addModel(VerilatedModel* modelp) {
    threadPoolp();  // Ensure thread pool is created, so m_threads cannot change any more

    if (modelp->threads() > m_threads) {
        std::ostringstream msg;
        msg << "VerilatedContext has " << m_threads << " threads but model '"
            << modelp->modelName() << "' (instantiated as '" << modelp->hierName()
            << "') was Verilated with --threads " << modelp->threads() << ".\n";
        const std::string str = msg.str();
        VL_FATAL_MT(__FILE__, __LINE__, modelp->hierName(), str.c_str());
    }
}

VerilatedVirtualBase* VerilatedContext::threadPoolp() {
    if (m_threads == 1) return nullptr;
#if VL_THREADED
    if (!m_threadPool) m_threadPool.reset(new VlThreadPool{this, m_threads - 1});
#endif
    return m_threadPool.get();
}

VerilatedVirtualBase*
VerilatedContext::enableExecutionProfiler(VerilatedVirtualBase* (*construct)(VerilatedContext&)) {
    if (!m_executionProfiler) m_executionProfiler.reset(construct(*this));
    return m_executionProfiler.get();
}

//======================================================================
// VerilatedContextImp:: Methods - command line

void VerilatedContextImp::commandArgsAddGuts(int argc, const char** argv) VL_REQUIRES(m_argMutex) {
    if (!m_args.m_argVecLoaded) m_args.m_argVec.clear();
    for (int i = 0; i < argc; ++i) {
        m_args.m_argVec.emplace_back(argv[i]);
        commandArgVl(argv[i]);
    }
    m_args.m_argVecLoaded = true;  // Can't just test later for empty vector, no arguments is ok
}
void VerilatedContextImp::commandArgDump() const VL_MT_SAFE_EXCLUDES(m_argMutex) {
    const VerilatedLockGuard lock{m_argMutex};
    VL_PRINTF_MT("  Argv:");
    for (const auto& i : m_args.m_argVec) VL_PRINTF_MT(" %s", i.c_str());
    VL_PRINTF_MT("\n");
}
std::string VerilatedContextImp::argPlusMatch(const char* prefixp)
    VL_MT_SAFE_EXCLUDES(m_argMutex) {
    const VerilatedLockGuard lock{m_argMutex};
    // Note prefixp does not include the leading "+"
    const size_t len = std::strlen(prefixp);
    if (VL_UNLIKELY(!m_args.m_argVecLoaded)) {
        m_args.m_argVecLoaded = true;  // Complain only once
        VL_FATAL_MT("unknown", 0, "",
                    "%Error: Verilog called $test$plusargs or $value$plusargs without"
                    " testbench C first calling Verilated::commandArgs(argc,argv).");
    }
    for (const auto& i : m_args.m_argVec) {
        if (i[0] == '+') {
            if (0 == std::strncmp(prefixp, i.c_str() + 1, len)) return i;
        }
    }
    return "";
}
// Return string representing current argv
// Only used by VPI so uses static storage, only supports most recent called context
std::pair<int, char**> VerilatedContextImp::argc_argv() VL_MT_SAFE_EXCLUDES(m_argMutex) {
    const VerilatedLockGuard lock{m_argMutex};
    static bool s_loaded = false;
    static int s_argc = 0;
    static char** s_argvp = nullptr;
    if (VL_UNLIKELY(!s_loaded)) {
        s_loaded = true;
        s_argc = m_args.m_argVec.size();
        s_argvp = new char*[s_argc + 1];
        int in = 0;
        for (const auto& i : m_args.m_argVec) {
            s_argvp[in] = new char[i.length() + 1];
            std::strcpy(s_argvp[in], i.c_str());
            ++in;
        }
        s_argvp[s_argc] = nullptr;
    }
    return std::make_pair(s_argc, s_argvp);
}

void VerilatedContextImp::commandArgVl(const std::string& arg) {
    if (0 == std::strncmp(arg.c_str(), "+verilator+", std::strlen("+verilator+"))) {
        std::string str;
        uint64_t u64;
        if (arg == "+verilator+debug") {
            Verilated::debug(4);
        } else if (commandArgVlUint64(arg, "+verilator+debugi+", u64, 0,
                                      std::numeric_limits<int>::max())) {
            Verilated::debug(static_cast<int>(u64));
        } else if (commandArgVlUint64(arg, "+verilator+error+limit+", u64, 0,
                                      std::numeric_limits<int>::max())) {
            errorLimit(static_cast<int>(u64));
        } else if (arg == "+verilator+help") {
            VerilatedImp::versionDump();
            VL_PRINTF_MT("For help, please see 'verilator --help'\n");
            VL_FATAL_MT("COMMAND_LINE", 0, "",
                        "Exiting due to command line argument (not an error)");
        } else if (arg == "+verilator+noassert") {
            assertOn(false);
        } else if (commandArgVlUint64(arg, "+verilator+prof+exec+start+", u64)
                   || commandArgVlUint64(arg, "+verilator+prof+threads+start+", u64)) {
            profExecStart(u64);
        } else if (commandArgVlUint64(arg, "+verilator+prof+exec+window+", u64, 1)
                   || commandArgVlUint64(arg, "+verilator+prof+threads+window+", u64, 1)) {
            profExecWindow(u64);
        } else if (commandArgVlString(arg, "+verilator+prof+exec+file+", str)
                   || commandArgVlString(arg, "+verilator+prof+threads+file+", str)) {
            profExecFilename(str);
        } else if (commandArgVlString(arg, "+verilator+prof+vlt+file+", str)) {
            profVltFilename(str);
        } else if (commandArgVlUint64(arg, "+verilator+rand+reset+", u64, 0, 2)) {
            randReset(static_cast<int>(u64));
        } else if (commandArgVlUint64(arg, "+verilator+seed+", u64, 1,
                                      std::numeric_limits<int>::max())) {
            randSeed(static_cast<int>(u64));
        } else if (arg == "+verilator+V") {
            VerilatedImp::versionDump();  // Someday more info too
            VL_FATAL_MT("COMMAND_LINE", 0, "",
                        "Exiting due to command line argument (not an error)");
        } else if (arg == "+verilator+version") {
            VerilatedImp::versionDump();
            VL_FATAL_MT("COMMAND_LINE", 0, "",
                        "Exiting due to command line argument (not an error)");
        } else {
            const std::string msg = "Unknown runtime argument: " + arg;
            VL_FATAL_MT("COMMAND_LINE", 0, "", msg.c_str());
        }
    }
}

bool VerilatedContextImp::commandArgVlString(const std::string& arg, const std::string& prefix,
                                             std::string& valuer) {
    const size_t len = prefix.length();
    if (0 == std::strncmp(prefix.c_str(), arg.c_str(), len)) {
        valuer = arg.substr(len);
        return true;
    } else {
        return false;
    }
}

bool VerilatedContextImp::commandArgVlUint64(const std::string& arg, const std::string& prefix,
                                             uint64_t& valuer, uint64_t min, uint64_t max) {
    std::string str;
    if (commandArgVlString(arg, prefix, str)) {
        const auto fail = [&](const std::string& extra = "") {
            std::stringstream ss;
            ss << "Argument '" << prefix << "' must be an unsigned integer";
            if (min != std::numeric_limits<uint64_t>::min()) ss << ", greater than " << min - 1;
            if (max != std::numeric_limits<uint64_t>::max()) ss << ", less than " << max + 1;
            if (!extra.empty()) ss << ". " << extra;
            const std::string& msg = ss.str();
            VL_FATAL_MT("COMMAND_LINE", 0, "", msg.c_str());
        };

        if (std::any_of(str.begin(), str.end(), [](int c) { return !std::isdigit(c); })) fail();
        char* end;
        valuer = std::strtoull(str.c_str(), &end, 10);
        if (errno == ERANGE) fail("Value out of range of uint64_t");
        if (valuer < min || valuer > max) fail();
        return true;
    }
    return false;
}

//======================================================================
// VerilatedContext:: + VerilatedContextImp:: Methods - random

void VerilatedContext::randSeed(int val) VL_MT_SAFE {
    // As we have per-thread state, the epoch must be static,
    // and so the rand seed's mutex must also be static
    const VerilatedLockGuard lock{VerilatedContextImp::s().s_randMutex};
    m_s.m_randSeed = val;
    const uint64_t newEpoch = VerilatedContextImp::s().s_randSeedEpoch + 1;
    // Obververs must see new epoch AFTER seed updated
#ifdef VL_THREADED
    std::atomic_signal_fence(std::memory_order_release);
#endif
    VerilatedContextImp::s().s_randSeedEpoch = newEpoch;
}
uint64_t VerilatedContextImp::randSeedDefault64() const VL_MT_SAFE {
    if (randSeed() != 0) {
        return ((static_cast<uint64_t>(randSeed()) << 32) ^ (static_cast<uint64_t>(randSeed())));
    } else {
        return ((static_cast<uint64_t>(vl_sys_rand32()) << 32)
                ^ (static_cast<uint64_t>(vl_sys_rand32())));
    }
}

//======================================================================
// VerilatedContext:: Methods - scopes

void VerilatedContext::scopesDump() const VL_MT_SAFE {
    const VerilatedLockGuard lock{m_impdatap->m_nameMutex};
    VL_PRINTF_MT("  scopesDump:\n");
    for (const auto& i : m_impdatap->m_nameMap) {
        const VerilatedScope* const scopep = i.second;
        scopep->scopeDump();
    }
    VL_PRINTF_MT("\n");
}

void VerilatedContextImp::scopeInsert(const VerilatedScope* scopep) VL_MT_SAFE {
    // Slow ok - called once/scope at construction
    const VerilatedLockGuard lock{m_impdatap->m_nameMutex};
    const auto it = m_impdatap->m_nameMap.find(scopep->name());
    if (it == m_impdatap->m_nameMap.end()) m_impdatap->m_nameMap.emplace(scopep->name(), scopep);
}
void VerilatedContextImp::scopeErase(const VerilatedScope* scopep) VL_MT_SAFE {
    // Slow ok - called once/scope at destruction
    const VerilatedLockGuard lock{m_impdatap->m_nameMutex};
    VerilatedImp::userEraseScope(scopep);
    const auto it = m_impdatap->m_nameMap.find(scopep->name());
    if (it != m_impdatap->m_nameMap.end()) m_impdatap->m_nameMap.erase(it);
}
const VerilatedScope* VerilatedContext::scopeFind(const char* namep) const VL_MT_SAFE {
    // Thread save only assuming this is called only after model construction completed
    const VerilatedLockGuard lock{m_impdatap->m_nameMutex};
    // If too slow, can assume this is only VL_MT_SAFE_POSINIT
    const auto& it = m_impdatap->m_nameMap.find(namep);
    if (VL_UNLIKELY(it == m_impdatap->m_nameMap.end())) return nullptr;
    return it->second;
}
const VerilatedScopeNameMap* VerilatedContext::scopeNameMap() VL_MT_SAFE {
    return &(impp()->m_impdatap->m_nameMap);
}

//======================================================================
// VerilatedSyms:: Methods

VerilatedSyms::VerilatedSyms(VerilatedContext* contextp)
    : _vm_contextp__(contextp ? contextp : Verilated::threadContextp()) {
    VerilatedContext::checkMagic(_vm_contextp__);
    Verilated::threadContextp(_vm_contextp__);
#ifdef VL_THREADED
    __Vm_evalMsgQp = new VerilatedEvalMsgQueue;
#endif
}

VerilatedSyms::~VerilatedSyms() {
    VerilatedContext::checkMagic(_vm_contextp__);
#ifdef VL_THREADED
    delete __Vm_evalMsgQp;
#endif
}

//===========================================================================
// Verilated:: Methods

void Verilated::debug(int level) VL_MT_SAFE {
    s_debug = level;
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

const char* Verilated::catName(const char* n1, const char* n2, const char* delimiter) VL_MT_SAFE {
    // Used by symbol table creation to make module names
    static VL_THREAD_LOCAL char* t_strp = nullptr;
    static VL_THREAD_LOCAL size_t t_len = 0;
    const size_t newlen = std::strlen(n1) + std::strlen(n2) + std::strlen(delimiter) + 1;
    if (VL_UNLIKELY(!t_strp || newlen > t_len)) {
        if (t_strp) delete[] t_strp;
        t_strp = new char[newlen];
        t_len = newlen;
    }
    char* dp = t_strp;
    for (const char* sp = n1; *sp;) *dp++ = *sp++;
    for (const char* sp = delimiter; *sp;) *dp++ = *sp++;
    for (const char* sp = n2; *sp;) *dp++ = *sp++;
    *dp++ = '\0';
    return t_strp;
}

//=========================================================================
// Flush and exit callbacks

// Keeping these out of class Verilated to avoid having to include <list>
// in verilated.h (for compilation speed)
using VoidPCbList = std::list<std::pair<Verilated::VoidPCb, void*>>;
static struct {
    VerilatedMutex s_flushMutex;
    VoidPCbList s_flushCbs VL_GUARDED_BY(s_flushMutex);
    VerilatedMutex s_exitMutex;
    VoidPCbList s_exitCbs VL_GUARDED_BY(s_exitMutex);
} VlCbStatic;

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
    const VerilatedLockGuard lock{VlCbStatic.s_flushMutex};
    addCb(cb, datap, VlCbStatic.s_flushCbs);
}
void Verilated::removeFlushCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock{VlCbStatic.s_flushMutex};
    removeCb(cb, datap, VlCbStatic.s_flushCbs);
}
void Verilated::runFlushCallbacks() VL_MT_SAFE {
    // Flush routines may call flush, so avoid mutex deadlock
#ifdef VL_THREADED
    static std::atomic<int> s_recursing;
#else
    static int s_recursing = 0;
#endif
    if (!s_recursing++) {
        const VerilatedLockGuard lock{VlCbStatic.s_flushMutex};
        runCallbacks(VlCbStatic.s_flushCbs);
    }
    --s_recursing;
    std::fflush(stderr);
    std::fflush(stdout);
    // When running internal code coverage (gcc --coverage, as opposed to
    // verilator --coverage), dump coverage data to properly cover failing
    // tests.
    VL_GCOV_DUMP();
}

void Verilated::addExitCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock{VlCbStatic.s_exitMutex};
    addCb(cb, datap, VlCbStatic.s_exitCbs);
}
void Verilated::removeExitCb(VoidPCb cb, void* datap) VL_MT_SAFE {
    const VerilatedLockGuard lock{VlCbStatic.s_exitMutex};
    removeCb(cb, datap, VlCbStatic.s_exitCbs);
}
void Verilated::runExitCallbacks() VL_MT_SAFE {
#ifdef VL_THREADED
    static std::atomic<int> s_recursing;
#else
    static int s_recursing = 0;
#endif
    if (!s_recursing++) {
        const VerilatedLockGuard lock{VlCbStatic.s_exitMutex};
        runCallbacks(VlCbStatic.s_exitCbs);
    }
    --s_recursing;
}

const char* Verilated::productName() VL_PURE { return VERILATOR_PRODUCT; }
const char* Verilated::productVersion() VL_PURE { return VERILATOR_VERSION; }

void Verilated::nullPointerError(const char* filename, int linenum) VL_MT_SAFE {
    // Slowpath - Called only on error
    VL_FATAL_MT(filename, linenum, "", "Null pointer dereferenced");
    VL_UNREACHABLE
}

void Verilated::overWidthError(const char* signame) VL_MT_SAFE {
    // Slowpath - Called only when signal sets too high of a bit
    const std::string msg = (std::string{"Testbench C set input '"} + signame
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

int Verilated::exportFuncNum(const char* namep) VL_MT_SAFE {
    return VerilatedImp::exportFind(namep);
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
// VerilatedImp:: Methods

void VerilatedImp::versionDump() VL_MT_SAFE {
    VL_PRINTF_MT("  Version: %s %s\n", Verilated::productName(), Verilated::productVersion());
}

//===========================================================================
// VerilatedModel:: Methods

VerilatedModel::VerilatedModel(VerilatedContext& context)
    : m_context{context} {}

std::unique_ptr<VerilatedTraceConfig> VerilatedModel::traceConfig() const { return nullptr; }

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
uint32_t VerilatedVarProps::entSize() const {
    uint32_t size = 1;
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
    const int indxAdj = indx - low(dim);
    uint8_t* bytep = reinterpret_cast<uint8_t*>(datap);
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
    Verilated::threadContextp()->impp()->scopeErase(this);
    if (m_namep) VL_DO_CLEAR(delete[] m_namep, m_namep = nullptr);
    if (m_callbacksp) VL_DO_CLEAR(delete[] m_callbacksp, m_callbacksp = nullptr);
    if (m_varsp) VL_DO_CLEAR(delete m_varsp, m_varsp = nullptr);
    m_funcnumMax = 0;  // Force callback table to empty
}

void VerilatedScope::configure(VerilatedSyms* symsp, const char* prefixp, const char* suffixp,
                               const char* identifier, int8_t timeunit,
                               const Type& type) VL_MT_UNSAFE {
    // Slowpath - called once/scope at construction
    // We don't want the space and reference-count access overhead of strings.
    m_symsp = symsp;
    m_type = type;
    m_timeunit = timeunit;
    {
        char* const namep = new char[std::strlen(prefixp) + std::strlen(suffixp) + 2];
        char* dp = namep;
        for (const char* sp = prefixp; *sp;) *dp++ = *sp++;
        if (*prefixp && *suffixp) *dp++ = '.';
        for (const char* sp = suffixp; *sp;) *dp++ = *sp++;
        *dp++ = '\0';
        m_namep = namep;
    }
    m_identifierp = identifier;
    Verilated::threadContextp()->impp()->scopeInsert(this);
}

void VerilatedScope::exportInsert(int finalize, const char* namep, void* cb) VL_MT_UNSAFE {
    // Slowpath - called once/scope*export at construction
    // Insert a exported function into scope table
    const int funcnum = VerilatedImp::exportInsert(namep);
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
            std::memset(m_callbacksp, 0, m_funcnumMax * sizeof(void*));
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

    if (!m_varsp) m_varsp = new VerilatedVarNameMap;
    VerilatedVar var(namep, datap, vltype, static_cast<VerilatedVarFlags>(vlflags), dims, isParam);

    va_list ap;
    va_start(ap, dims);
    for (int i = 0; i < dims; ++i) {
        const int msb = va_arg(ap, int);
        const int lsb = va_arg(ap, int);
        if (i == 0) {
            var.m_packed.m_left = msb;
            var.m_packed.m_right = lsb;
        } else if (i >= 1 && i <= var.udims()) {
            var.m_unpacked[i - 1].m_left = msb;
            var.m_unpacked[i - 1].m_right = lsb;
        } else {
            // We could have a linked list of ranges, but really this whole thing needs
            // to be generalized to support structs and unions, etc.
            const std::string msg
                = std::string{"Unsupported multi-dimensional public varInsert: "} + namep;
            VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
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
    const std::string msg
        = (std::string{"Testbench C called '"} + VerilatedImp::exportName(funcnum)
           + "' but scope wasn't set, perhaps due to dpi import call without "
           + "'context', or missing svSetScope. See IEEE 1800-2017 35.5.3.");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
    return nullptr;
}

void* VerilatedScope::exportFindError(int funcnum) const {
    // Slowpath - Called only when find has failed
    const std::string msg
        = (std::string{"Testbench C called '"} + VerilatedImp::exportName(funcnum)
           + "' but this DPI export function exists only in other scopes, not scope '" + name()
           + "'");
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
    if (const VerilatedVarNameMap* const varsp = this->varsp()) {
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
