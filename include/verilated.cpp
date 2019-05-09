// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
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
/// \brief Verilator: Linked against all applications using Verilated source.
///
///     This file must be compiled and linked against all objects
///     created from Verilator.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#define _VERILATED_CPP_

#include "verilatedos.h"
#include "verilated_imp.h"

#include "verilated_config.h"

#include <cctype>
#include <sys/stat.h>  // mkdir

#if defined(_WIN32) || defined(__MINGW32__)
# include <direct.h>  // mkdir
#endif

#define VL_VALUE_STRING_MAX_WIDTH 8192  ///< Max static char array for VL_VALUE_STRING

//===========================================================================
// Static sanity checks (when get C++11 can use static_assert)

typedef union {
    char vluint8_incorrect[(sizeof(vluint8_t) == 1) ? 1:-1];
    char vluint16_incorrect[(sizeof(vluint16_t) == 2) ? 1:-1];
    char vluint32_incorrect[(sizeof(vluint32_t) == 4) ? 1:-1];
    char vluint64_incorrect[(sizeof(vluint64_t) == 8) ? 1:-1];
} vl_static_checks_t;

//===========================================================================
// Global variables

// Slow path variables
VerilatedMutex Verilated::m_mutex;
VerilatedVoidCb Verilated::s_flushCb = NULL;

// Keep below together in one cache line
Verilated::Serialized Verilated::s_s;
Verilated::NonSerialized Verilated::s_ns;
VL_THREAD_LOCAL Verilated::ThreadLocal Verilated::t_s;

Verilated::CommandArgValues Verilated::s_args;

VerilatedImp VerilatedImp::s_s;

//===========================================================================
// User definable functions

#ifndef VL_USER_FINISH  ///< Define this to override this function
void vl_finish(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    if (0 && hier) {}
    VL_PRINTF("- %s:%d: Verilog $finish\n", filename, linenum);  // Not VL_PRINTF_MT, already on main thread
    if (Verilated::gotFinish()) {
        VL_PRINTF("- %s:%d: Second verilog $finish, exiting\n", filename, linenum);  // Not VL_PRINTF_MT, already on main thread
        Verilated::flushCall();
        exit(0);
    }
    Verilated::gotFinish(true);
}
#endif

#ifndef VL_USER_STOP  ///< Define this to override this function
void vl_stop(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    Verilated::gotFinish(true);
    Verilated::flushCall();
    vl_fatal(filename, linenum, hier, "Verilog $stop");
}
#endif

#ifndef VL_USER_FATAL  ///< Define this to override this function
void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_UNSAFE {
    if (0 && hier) {}
    Verilated::gotFinish(true);
    VL_PRINTF("%%Error: %s:%d: %s\n", filename, linenum, msg);  // Not VL_PRINTF_MT, already on main thread
    Verilated::flushCall();

    VL_PRINTF("Aborting...\n");  // Not VL_PRINTF_MT, already on main thread
    Verilated::flushCall();  // Second flush in case VL_PRINTF does something needing a flush
    abort();
}
#endif

//===========================================================================
// Wrapper to call certain functions via messages when multithreaded

void VL_FINISH_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg([=](){
                vl_finish(filename, linenum, hier);
            }));
#else
    vl_finish(filename, linenum, hier);
#endif
}

void VL_STOP_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg([=](){
                vl_stop(filename, linenum, hier);
            }));
#else
    vl_stop(filename, linenum, hier);
#endif
}

void VL_FATAL_MT(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_SAFE {
#ifdef VL_THREADED
    VerilatedThreadMsgQueue::post(VerilatedMsg([=](){
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
    int len = VL_VSNPRINTF(NULL, 0, formatp, aq);
    va_end(aq);
    if (VL_UNLIKELY(len < 1)) {
        return "";
    }

    char* bufp = new char[len+1];
    VL_VSNPRINTF(bufp, len+1, formatp, ap);

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
    // Alternative is to use std::this_thread::get_id, but that returns a hard-to-read number and is very slow
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
    // printf("-imm-V{t%d,%" VL_PRI64 "d}%s", VL_THREAD_ID(), _vl_dbg_sequence_number(), out.c_str());

    // Using VL_PRINTF not VL_PRINTF_MT so that we can call VL_DBG_MSGF
    // from within the guts of the thread execution machinery (and it goes
    // to the screen and not into the queues we're debugging)
    VL_PRINTF("-V{t%d,%" VL_PRI64 "u}%s", VL_THREAD_ID(), _vl_dbg_sequence_number(), out.c_str());
}

#ifdef VL_THREADED
void VL_PRINTF_MT(const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    std::string out = _vl_string_vprintf(formatp, ap);
    va_end(ap);
    VerilatedThreadMsgQueue::post(VerilatedMsg([=](){
                VL_PRINTF("%s", out.c_str());
            }));
}
#endif

//===========================================================================
// Overall class init

Verilated::Serialized::Serialized() {
    s_randReset = 0;
    s_randSeed = 0;
    s_debug = 0;
    s_calcUnusedSigs = false;
    s_gotFinish = false;
    s_assertOn = true;
    s_fatalOnVpiError = true;  // retains old default behaviour
}

Verilated::NonSerialized::NonSerialized() {
    s_profThreadsStart = 1;
    s_profThreadsWindow = 2;
    s_profThreadsFilenamep = strdup("profile_threads.dat");
}
Verilated::NonSerialized::~NonSerialized() {
    if (s_profThreadsFilenamep) {
        free(const_cast<char*>(s_profThreadsFilenamep)); s_profThreadsFilenamep=NULL;
    }
}

//===========================================================================
// Random -- Mostly called at init time, so not inline.

static vluint32_t vl_sys_rand32() VL_MT_UNSAFE {
    // Return random 32-bits using system library.
    // Used only to construct seed for Verilator's PNRG.
#if defined(_WIN32) && !defined(__CYGWIN__)
    // Windows doesn't have lrand48(), although Cygwin does.
    return (rand()<<16) ^ rand();
#else
    return (lrand48()<<16) ^ lrand48();
#endif
}

vluint64_t vl_rand64() VL_MT_SAFE {
    static VerilatedMutex s_mutex;
    static VL_THREAD_LOCAL bool t_seeded = false;
    static VL_THREAD_LOCAL vluint64_t t_state[2];
    if (VL_UNLIKELY(!t_seeded)) {
        t_seeded = true;
        {
            VerilatedLockGuard lock(s_mutex);
            if (Verilated::randSeed() != 0) {
                t_state[0] = ((static_cast<vluint64_t>(Verilated::randSeed()) << 32)
                              ^ (static_cast<vluint64_t>(Verilated::randSeed())));
                t_state[1] = ((static_cast<vluint64_t>(Verilated::randSeed()) << 32)
                              ^ (static_cast<vluint64_t>(Verilated::randSeed())));
            } else {
                t_state[0] = ((static_cast<vluint64_t>(vl_sys_rand32()) << 32)
                              ^ (static_cast<vluint64_t>(vl_sys_rand32())));
                t_state[1] = ((static_cast<vluint64_t>(vl_sys_rand32()) << 32)
                              ^ (static_cast<vluint64_t>(vl_sys_rand32())));
            }
            // Fix state as algorithm is slow to randomize if many zeros
            // This causes a loss of ~ 1 bit of seed entropy, no big deal
            if (VL_COUNTONES_I(t_state[0]) < 10) t_state[0] = ~t_state[0];
            if (VL_COUNTONES_I(t_state[1]) < 10) t_state[1] = ~t_state[1];
        }
    }
    // Xoroshiro128+ algorithm
    vluint64_t result = t_state[0] + t_state[1];
    t_state[1] ^= t_state[0];
    t_state[0] = (((t_state[0] << 55) | (t_state[0] >> 9))
                  ^ t_state[1] ^ (t_state[1] << 14));
    t_state[1] = (t_state[1] << 36) | (t_state[1] >> 28);
    return result;
}

IData VL_RANDOM_I(int obits) VL_MT_SAFE {
    return vl_rand64() & VL_MASK_I(obits);
}
QData VL_RANDOM_Q(int obits) VL_MT_SAFE {
    return vl_rand64() & VL_MASK_Q(obits);
}
WDataOutP VL_RANDOM_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i=0; i<VL_WORDS_I(obits); ++i) {
        if (i<(VL_WORDS_I(obits)-1)) {
            outwp[i] = vl_rand64();
        } else {
            outwp[i] = vl_rand64() & VL_MASK_I(obits);
        }
    }
    return outwp;
}

IData VL_RAND_RESET_I(int obits) VL_MT_SAFE {
    if (Verilated::randReset()==0) return 0;
    IData data = ~0;
    if (Verilated::randReset()!=1) {  // if 2, randomize
        data = VL_RANDOM_I(obits);
    }
    if (obits<32) data &= VL_MASK_I(obits);
    return data;
}
QData VL_RAND_RESET_Q(int obits) VL_MT_SAFE {
    if (Verilated::randReset()==0) return 0;
    QData data = VL_ULL(~0);
    if (Verilated::randReset()!=1) {  // if 2, randomize
        data = VL_RANDOM_Q(obits);
    }
    if (obits<64) data &= VL_MASK_Q(obits);
    return data;
}
WDataOutP VL_RAND_RESET_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i=0; i<VL_WORDS_I(obits); ++i) {
        if (i<(VL_WORDS_I(obits)-1)) {
            outwp[i] = VL_RAND_RESET_I(32);
        } else {
            outwp[i] = VL_RAND_RESET_I(32) & VL_MASK_I(obits);
        }
    }
    return outwp;
}

WDataOutP VL_ZERO_RESET_W(int obits, WDataOutP outwp) VL_MT_SAFE {
    for (int i=0; i<VL_WORDS_I(obits); ++i) outwp[i] = 0;
    return outwp;
}

//===========================================================================
// Debug

void _VL_DEBUG_PRINT_W(int lbits, WDataInP iwp) VL_MT_SAFE {
    VL_PRINTF_MT("  Data: w%d: ", lbits);
    for (int i=VL_WORDS_I(lbits)-1; i>=0; --i) { VL_PRINTF_MT("%08x ", iwp[i]); }
    VL_PRINTF_MT("\n");
}

//===========================================================================
// Slow math

WDataOutP _vl_moddiv_w(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp, bool is_modulus) VL_MT_SAFE {
    // See Knuth Algorithm D.  Computes u/v = q.r
    // This isn't massively tuned, as wide division is rare
    // for debug see V3Number version
    // Requires clean input
    int words = VL_WORDS_I(lbits);
    for (int i=0; i<words; ++i) owp[i]=0;
    // Find MSB and check for zero.
    int umsbp1 = VL_MOSTSETBITP1_W(words, lwp);  // dividend
    int vmsbp1 = VL_MOSTSETBITP1_W(words, rwp);  // divisor
    if (VL_UNLIKELY(vmsbp1==0)  // rwp==0 so division by zero.  Return 0.
        || VL_UNLIKELY(umsbp1==0)) {  // 0/x so short circuit and return 0
        return owp;
    }

    int uw = VL_WORDS_I(umsbp1);  // aka "m" in the algorithm
    int vw = VL_WORDS_I(vmsbp1);  // aka "n" in the algorithm

    if (vw == 1) {  // Single divisor word breaks rest of algorithm
        vluint64_t k = 0;
        for (int j = uw-1; j >= 0; --j) {
            vluint64_t unw64 = ((k<<VL_ULL(32)) + static_cast<vluint64_t>(lwp[j]));
            owp[j] = unw64 / static_cast<vluint64_t>(rwp[0]);
            k      = unw64 - static_cast<vluint64_t>(owp[j])*static_cast<vluint64_t>(rwp[0]);
        }
        if (is_modulus) {
            owp[0] = k;
            for (int i=1; i<words; ++i) owp[i]=0;
        }
        return owp;
    }

    // +1 word as we may shift during normalization
    vluint32_t un[VL_MULS_MAX_WORDS+1];  // Fixed size, as MSVC++ doesn't allow [words] here
    vluint32_t vn[VL_MULS_MAX_WORDS+1];  // v normalized

    // Zero for ease of debugging and to save having to zero for shifts
    // Note +1 as loop will use extra word
    for (int i=0; i<words+1; ++i) { un[i]=vn[i]=0; }

    // Algorithm requires divisor MSB to be set
    // Copy and shift to normalize divisor so MSB of vn[vw-1] is set
    int s = 31-VL_BITBIT_I(vmsbp1-1);  // shift amount (0...31)
    vluint32_t shift_mask = s ? 0xffffffff : 0;  // otherwise >> 32 won't mask the value
    for (int i = vw-1; i>0; --i) {
        vn[i] = (rwp[i] << s) | (shift_mask & (rwp[i-1] >> (32-s)));
    }
    vn[0] = rwp[0] << s;

    // Copy and shift dividend by same amount; may set new upper word
    if (s) un[uw] = lwp[uw-1] >> (32-s);
    else un[uw] = 0;
    for (int i=uw-1; i>0; --i) {
        un[i] = (lwp[i] << s) | (shift_mask & (lwp[i-1] >> (32-s)));
    }
    un[0] = lwp[0] << s;

    // Main loop
    for (int j = uw - vw; j >= 0; --j) {
        // Estimate
        vluint64_t unw64 = (static_cast<vluint64_t>(un[j+vw])<<VL_ULL(32) | static_cast<vluint64_t>(un[j+vw-1]));
        vluint64_t qhat = unw64 / static_cast<vluint64_t>(vn[vw-1]);
        vluint64_t rhat = unw64 - qhat*static_cast<vluint64_t>(vn[vw-1]);

      again:
        if (qhat >= VL_ULL(0x100000000)
            || ((qhat*vn[vw-2]) > ((rhat<<VL_ULL(32)) + un[j+vw-2]))) {
            qhat = qhat - 1;
            rhat = rhat + vn[vw-1];
            if (rhat < VL_ULL(0x100000000)) goto again;
        }

        vlsint64_t t = 0;  // Must be signed
        vluint64_t k = 0;
        for (int i=0; i<vw; ++i) {
            vluint64_t p = qhat*vn[i];  // Multiply by estimate
            t = un[i+j] - k - (p & VL_ULL(0xFFFFFFFF));  // Subtract
            un[i+j] = t;
            k = (p >> VL_ULL(32)) - (t >> VL_ULL(32));
        }
        t = un[j+vw] - k;
        un[j+vw] = t;
        owp[j] = qhat;  // Save quotient digit

        if (t < 0) {
            // Over subtracted; correct by adding back
            owp[j]--;
            k = 0;
            for (int i=0; i<vw; ++i) {
                t = static_cast<vluint64_t>(un[i+j]) + static_cast<vluint64_t>(vn[i]) + k;
                un[i+j] = t;
                k = t >> VL_ULL(32);
            }
            un[j+vw] = un[j+vw] + k;
        }
    }

    if (is_modulus) {  // modulus
        // Need to reverse normalization on copy to output
        for (int i=0; i<vw; ++i) {
            owp[i] = (un[i] >> s) | (shift_mask & (un[i+1] << (32-s)));
        }
        for (int i=vw; i<words; ++i) owp[i] = 0;
        return owp;
    } else {  // division
        return owp;
    }
}

WDataOutP VL_POW_WWW(int obits, int, int rbits, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    // obits==lbits, rbits can be different
    owp[0] = 1;
    for (int i=1; i < VL_WORDS_I(obits); i++) owp[i] = 0;
    // cppcheck-suppress variableScope
    WData powstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    WData lastpowstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    WData lastoutstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    // cppcheck-suppress variableScope
    VL_ASSIGN_W(obits, powstore, lwp);
    for (int bit=0; bit<rbits; bit++) {
        if (bit>0) {  // power = power*power
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
WDataOutP VL_POW_WWQ(int obits, int lbits, int rbits, WDataOutP owp, WDataInP lwp, QData rhs) VL_MT_SAFE {
    WData rhsw[2];  VL_SET_WQ(rhsw, rhs);
    return VL_POW_WWW(obits, lbits, rbits, owp, lwp, rhsw);
}
QData VL_POW_QQW(int, int, int rbits, QData lhs, WDataInP rwp) VL_MT_SAFE {
    // Skip check for rhs == 0, as short-circuit doesn't save time
    if (VL_UNLIKELY(lhs==0)) return 0;
    QData power = lhs;
    QData out = VL_ULL(1);
    for (int bit=0; bit<rbits; ++bit) {
        if (bit>0) power = power*power;
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
        IData lor = 0;  // 0=all zeros, ~0=all ones, else mix
        for (int i=1; i < (words-1); ++i) {
            lor |= lwp[i];
        }
        lor |= ( (lwp[words-1] == VL_MASK_I(rbits)) ? ~VL_UL(0) : 0);
        if (lor==0 && lwp[0]==0) { return owp; }  // "X" so return 0
        else if (lor==0 && lwp[0]==1) { owp[0] = 1; return owp; }  // 1
        else if (lsign && lor == ~VL_UL(0) && lwp[0]==~VL_UL(0)) {  // -1
            if (rwp[0] & 1) { return VL_ALLONES_W(obits, owp); }  // -1^odd=-1
            else { owp[0] = 1; return owp; }  // -1^even=1
        }
        return 0;
    }
    return VL_POW_WWW(obits, rbits, rbits, owp, lwp, rwp);
}
WDataOutP VL_POWSS_WWQ(int obits, int lbits, int rbits,
                       WDataOutP owp, WDataInP lwp, QData rhs,
                       bool lsign, bool rsign) VL_MT_SAFE {
    WData rhsw[2];  VL_SET_WQ(rhsw, rhs);
    return VL_POWSS_WWW(obits, lbits, rbits, owp, lwp, rhsw, lsign, rsign);
}
QData VL_POWSS_QQW(int obits, int, int rbits, QData lhs, WDataInP rwp, bool lsign, bool rsign) VL_MT_SAFE {
    // Skip check for rhs == 0, as short-circuit doesn't save time
    if (rsign && VL_SIGN_W(rbits, rwp)) {
        if (lhs==0) return 0;  // "X"
        else if (lhs==1) return 1;
        else if (lsign && lhs==VL_MASK_I(obits)) {  // -1
            if (rwp[0] & 1) return VL_MASK_I(obits);  // -1^odd=-1
            else return 1;  // -1^even=1
        }
        return 0;
    }
    return VL_POW_QQW(obits, rbits, rbits, lhs, rwp);
}

//===========================================================================
// Formatting

/// Output a string representation of a wide number
std::string VL_DECIMAL_NW(int width, WDataInP lwp) VL_MT_SAFE {
    int maxdecwidth = (width+3)*4/3;
    // Or (maxdecwidth+7)/8], but can't have more than 4 BCD bits per word
    WData bcd[VL_VALUE_STRING_MAX_WIDTH/4+2];
    VL_ZERO_RESET_W(maxdecwidth, bcd);
    WData tmp[VL_VALUE_STRING_MAX_WIDTH/4+2];
    WData tmp2[VL_VALUE_STRING_MAX_WIDTH/4+2];
    int from_bit = width-1;
    // Skip all leading zeros
    for (; from_bit >= 0 && !(VL_BITRSHIFT_W(lwp, from_bit) & 1); --from_bit);
    // Double-dabble algorithm
    for (; from_bit >= 0; --from_bit) {
        // Any digits >= 5 need an add 3 (via tmp)
        for (int nibble_bit = 0; nibble_bit < maxdecwidth; nibble_bit+=4) {
            if ((VL_BITRSHIFT_W(bcd, nibble_bit) & 0xf) >= 5) {
                VL_ZERO_RESET_W(maxdecwidth, tmp2);
                tmp2[VL_BITWORD_I(nibble_bit)] |= 0x3 << VL_BITBIT_I(nibble_bit);
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
    int lsb = (maxdecwidth-1) & ~3;
    for (; lsb>0; lsb-=4) {  // Skip leading zeros
        if (VL_BITRSHIFT_W(bcd, lsb) & 0xf) break;
    }
    for (; lsb>=0; lsb-=4) {
        output += ('0' + (VL_BITRSHIFT_W(bcd, lsb) & 0xf));  // 0..9
    }
    return output;
}

// Do a va_arg returning a quad, assuming input argument is anything less than wide
#define _VL_VA_ARG_Q(ap, bits) (((bits) <= VL_WORDSIZE) ? va_arg(ap, IData) : va_arg(ap, QData))

void _vl_vsformat(std::string& output, const char* formatp, va_list ap) VL_MT_SAFE {
    // Format a Verilog $write style format into the output list
    // The format must be pre-processed (and lower cased) by Verilator
    // Arguments are in "width, arg-value (or WDataIn* if wide)" form
    //
    // Note uses a single buffer internally; presumes only one usage per printf
    // Note also assumes variables < 64 are not wide, this assumption is
    // sometimes not true in low-level routines written here in verilated.cpp
    static VL_THREAD_LOCAL char tmp[VL_VALUE_STRING_MAX_WIDTH];
    static VL_THREAD_LOCAL char tmpf[VL_VALUE_STRING_MAX_WIDTH];
    const char* pctp = NULL;  // Most recent %##.##g format
    bool inPct = false;
    bool widthSet = false;
    int width = 0;
    for (const char* pos = formatp; *pos; ++pos) {
        if (!inPct && pos[0]=='%') {
            pctp = pos;
            inPct = true;
            widthSet = false;
            width = 0;
        } else if (!inPct) {  // Normal text
            // Fast-forward to next escape and add to output
            const char *ep = pos;
            while (ep[0] && ep[0]!='%') ep++;
            if (ep != pos) {
                output.append(pos, ep-pos);
                pos += ep-pos-1;
            }
        } else {  // Format character
            inPct = false;
            char fmt = pos[0];
            switch (fmt) {
            case '0': case '1': case '2': case '3': case '4':
            case '5': case '6': case '7': case '8': case '9':
                inPct = true;  // Get more digits
                widthSet = true;
                width = width*10 + (fmt - '0');
                break;
            case '.':
                inPct = true;  // Get more digits
                break;
            case '%':
                output += '%';
                break;
            case 'N': {  // "C" string with name of module, add . if needed
                const char* cstrp = va_arg(ap, const char*);
                if (VL_LIKELY(*cstrp)) { output += cstrp; output += '.'; }
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
                output += *cstrp;
                break;
            }
            case 'e':
            case 'f':
            case 'g': {
                const int lbits = va_arg(ap, int);
                double d = va_arg(ap, double);
                if (lbits) {}  // UNUSED - always 64
                strncpy(tmpf, pctp, pos-pctp+1);
                tmpf[pos-pctp+1] = '\0';
                sprintf(tmp, tmpf, d);
                output += tmp;
                break;
            }
            default: {
                // Deal with all read-and-print somethings
                const int lbits = va_arg(ap, int);
                QData ld = 0;
                WData qlwp[2];
                WDataInP lwp;
                if (lbits <= VL_QUADSIZE) {
                    ld = _VL_VA_ARG_Q(ap, lbits);
                    VL_SET_WQ(qlwp, ld);
                    lwp = qlwp;
                } else {
                    lwp = va_arg(ap, WDataInP);
                    ld = lwp[0];
                }
                int lsb=lbits-1;
                if (widthSet && width==0) while (lsb && !VL_BITISSET_W(lwp, lsb)) --lsb;
                switch (fmt) {
                case 'c': {
                    IData charval = ld & 0xff;
                    output += charval;
                    break;
                }
                case 's':
                    for (; lsb>=0; --lsb) {
                        lsb = (lsb / 8) * 8;  // Next digit
                        IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xff;
                        output += (charval==0)?' ':charval;
                    }
                    break;
                case 'd': {  // Signed decimal
                    int digits;
                    std::string append;
                    if (lbits <= VL_QUADSIZE) {
                        digits = sprintf(tmp, "%" VL_PRI64 "d",
                                         static_cast<vlsint64_t>(VL_EXTENDS_QQ(lbits, lbits, ld)));
                        append = tmp;
                    } else {
                        if (VL_SIGN_I(lbits, lwp[VL_WORDS_I(lbits)-1])) {
                            WData neg[VL_VALUE_STRING_MAX_WIDTH/4+2];
                            VL_NEGATE_W(VL_WORDS_I(lbits), neg, lwp);
                            append = std::string("-") + VL_DECIMAL_NW(lbits, neg);
                        } else {
                            append = VL_DECIMAL_NW(lbits, lwp);
                        }
                        digits = append.length();
                    }
                    int needmore = width-digits;
                    if (needmore>0) {
                        if (pctp && pctp[0] && pctp[1]=='0') {  // %0
                            output.append(needmore, '0');  // Pre-pad zero
                        } else {
                            output.append(needmore, ' ');  // Pre-pad spaces
                        }
                    }
                    output += append;
                    break;
                }
                case '#': {  // Unsigned decimal
                    int digits;
                    std::string append;
                    if (lbits <= VL_QUADSIZE) {
                        digits = sprintf(tmp, "%" VL_PRI64 "u", ld);
                        append = tmp;
                    } else {
                        append = VL_DECIMAL_NW(lbits, lwp);
                        digits = append.length();
                    }
                    int needmore = width-digits;
                    if (needmore>0) {
                        if (pctp && pctp[0] && pctp[1]=='0') {  // %0
                            output.append(needmore, '0');  // Pre-pad zero
                        } else {
                            output.append(needmore, ' ');  // Pre-pad spaces
                        }
                    }
                    output += append;
                    break;
                }
                case 't': {  // Time
                    int digits;
                    if (VL_TIME_MULTIPLIER==1) {
                        digits=sprintf(tmp, "%" VL_PRI64 "u", ld);
                    } else if (VL_TIME_MULTIPLIER==1000) {
                        digits=sprintf(tmp, "%" VL_PRI64 "u.%03" VL_PRI64 "u",
                                       static_cast<QData>(ld/VL_TIME_MULTIPLIER),
                                       static_cast<QData>(ld%VL_TIME_MULTIPLIER));
                    } else {
                        VL_FATAL_MT(__FILE__, __LINE__, "", "Unsupported VL_TIME_MULTIPLIER");
                    }
                    int needmore = width-digits;
                    if (needmore>0) output.append(needmore, ' ');  // Pre-pad spaces
                    output += tmp;
                    break;
                }
                case 'b':
                    for (; lsb>=0; --lsb) {
                        output += (VL_BITRSHIFT_W(lwp, lsb) & 1) + '0';
                    }
                    break;
                case 'o':
                    for (; lsb>=0; --lsb) {
                        lsb = (lsb / 3) * 3;  // Next digit
                        // Octal numbers may span more than one wide word,
                        // so we need to grab each bit separately and check for overrun
                        // Octal is rare, so we'll do it a slow simple way
                        output += ('0'
                                   + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb+0)) ? 1 : 0)
                                   + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb+1)) ? 2 : 0)
                                   + ((VL_BITISSETLIMIT_W(lwp, lbits, lsb+2)) ? 4 : 0));
                    }
                    break;
                case 'u':  // Packed 2-state
                    output.reserve(output.size() + 4*VL_WORDS_I(lbits));
                    for (int i=0; i<VL_WORDS_I(lbits); ++i) {
                        output += static_cast<char>((lwp[i]     ) & 0xff);
                        output += static_cast<char>((lwp[i] >> 8) & 0xff);
                        output += static_cast<char>((lwp[i] >> 16) & 0xff);
                        output += static_cast<char>((lwp[i] >> 24) & 0xff);
                    }
                    break;
                case 'z':  // Packed 4-state
                    output.reserve(output.size() + 8*VL_WORDS_I(lbits));
                    for (int i=0; i<VL_WORDS_I(lbits); ++i) {
                        output += static_cast<char>((lwp[i]     ) & 0xff);
                        output += static_cast<char>((lwp[i] >> 8) & 0xff);
                        output += static_cast<char>((lwp[i] >> 16) & 0xff);
                        output += static_cast<char>((lwp[i] >> 24) & 0xff);
                        output += "\0\0\0\0";  // No tristate
                    }
                    break;
                case 'v':  // Strength; assume always strong
                    for (lsb=lbits-1; lsb>=0; --lsb) {
                        if (VL_BITRSHIFT_W(lwp, lsb) & 1) output += "St1 ";
                        else output += "St0 ";
                    }
                    break;
                case 'x':
                    for (; lsb>=0; --lsb) {
                        lsb = (lsb / 4) * 4;  // Next digit
                        IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xf;
                        output += "0123456789abcdef"[charval];
                    }
                    break;
                default:
                    std::string msg = std::string("Unknown _vl_vsformat code: ")+pos[0];
                    VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
                    break;
                }  // switch
            }
            }  // switch
        }
    }
}

static inline bool _vl_vsss_eof(FILE* fp, int& floc) VL_MT_SAFE {
    if (fp) return feof(fp) ? 1 : 0;  // 1:0 to prevent MSVC++ warning
    else return (floc<0);
}
static inline void _vl_vsss_advance(FILE* fp, int& floc) VL_MT_SAFE {
    if (fp) fgetc(fp);
    else floc -= 8;
}
static inline int  _vl_vsss_peek(FILE* fp, int& floc, WDataInP fromp, const std::string& fstr) VL_MT_SAFE {
    // Get a character without advancing
    if (fp) {
        int data = fgetc(fp);
        if (data == EOF) return EOF;
        ungetc(data, fp);
        return data;
    } else {
        if (floc < 0) return EOF;
        floc = floc & ~7;  // Align to closest character
        if (fromp == NULL) {
            return fstr[fstr.length()-1 - (floc>>3)];
        } else {
            return VL_BITRSHIFT_W(fromp, floc) & 0xff;
        }
    }
}
static inline void _vl_vsss_skipspace(FILE* fp, int& floc, WDataInP fromp, const std::string& fstr) VL_MT_SAFE {
    while (1) {
        int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c==EOF || !isspace(c)) return;
        _vl_vsss_advance(fp, floc);
    }
}
static inline void _vl_vsss_read(FILE* fp, int& floc, WDataInP fromp, const std::string& fstr,
                                 char* tmpp, const char* acceptp) VL_MT_SAFE {
    // Read into tmp, consisting of characters from acceptp list
    char* cp = tmpp;
    while (1) {
        int c = _vl_vsss_peek(fp, floc, fromp, fstr);
        if (c==EOF || isspace(c)) break;
        if (acceptp  // String - allow anything
            && NULL==strchr(acceptp, c)) break;
        if (acceptp) c = tolower(c);  // Non-strings we'll simplify
        *cp++ = c;
        _vl_vsss_advance(fp, floc);
    }
    *cp++ = '\0';
    //VL_DBG_MSGF(" _read got='"<<tmpp<<"'\n");
}
static inline void _vl_vsss_setbit(WDataOutP owp, int obits, int lsb, int nbits, IData ld) VL_MT_SAFE {
    for (; nbits && lsb<obits; nbits--, lsb++, ld>>=1) {
        VL_ASSIGNBIT_WI(0, lsb, owp, ld & 1);
    }
}
static inline void _vl_vsss_based(WDataOutP owp, int obits, int baseLog2,
                                  const char* strp, size_t posstart, size_t posend) VL_MT_SAFE {
    // Read in base "2^^baseLog2" digits from strp[posstart..posend-1] into owp of size obits.
    int lsb = 0;
    for (int i=0, pos=static_cast<int>(posend)-1; i<obits && pos>=static_cast<int>(posstart); --pos) {
        switch (tolower (strp[pos])) {
        case 'x': case 'z': case '?':  // FALLTHRU
        case '0': lsb += baseLog2; break;
        case '1': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  1); lsb+=baseLog2; break;
        case '2': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  2); lsb+=baseLog2; break;
        case '3': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  3); lsb+=baseLog2; break;
        case '4': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  4); lsb+=baseLog2; break;
        case '5': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  5); lsb+=baseLog2; break;
        case '6': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  6); lsb+=baseLog2; break;
        case '7': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  7); lsb+=baseLog2; break;
        case '8': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  8); lsb+=baseLog2; break;
        case '9': _vl_vsss_setbit(owp, obits, lsb, baseLog2,  9); lsb+=baseLog2; break;
        case 'a': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 10); lsb+=baseLog2; break;
        case 'b': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 11); lsb+=baseLog2; break;
        case 'c': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 12); lsb+=baseLog2; break;
        case 'd': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 13); lsb+=baseLog2; break;
        case 'e': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 14); lsb+=baseLog2; break;
        case 'f': _vl_vsss_setbit(owp, obits, lsb, baseLog2, 15); lsb+=baseLog2; break;
        case '_': break;
        }
    }
}

IData _vl_vsscanf(FILE* fp,  // If a fscanf
                  int fbits, WDataInP fromp,  // Else if a sscanf
                  const std::string& fstr,  // if a sscanf to string
                  const char* formatp, va_list ap) VL_MT_SAFE {
    // Read a Verilog $sscanf/$fscanf style format into the output list
    // The format must be pre-processed (and lower cased) by Verilator
    // Arguments are in "width, arg-value (or WDataIn* if wide)" form
    static VL_THREAD_LOCAL char tmp[VL_VALUE_STRING_MAX_WIDTH];
    int floc = fbits - 1;
    IData got = 0;
    bool inPct = false;
    const char* pos = formatp;
    for (; *pos && !_vl_vsss_eof(fp, floc); ++pos) {
        //VL_DBG_MSGF("_vlscan fmt='"<<pos[0]<<"' floc="<<floc<<" file='"<<_vl_vsss_peek(fp, floc, fromp, fstr)<<"'"<<endl);
        if (!inPct && pos[0]=='%') {
            inPct = true;
        } else if (!inPct && isspace(pos[0])) {  // Format spaces
            while (isspace(pos[1])) pos++;
            _vl_vsss_skipspace(fp, floc, fromp, fstr);
        } else if (!inPct) {  // Expected Format
            _vl_vsss_skipspace(fp, floc, fromp, fstr);
            int c = _vl_vsss_peek(fp, floc, fromp, fstr);
            if (c != pos[0]) goto done;
            else _vl_vsss_advance(fp, floc);
        } else {  // Format character
            // Skip loading spaces
            inPct = false;
            char fmt = pos[0];
            switch (fmt) {
            case '%': {
                int c = _vl_vsss_peek(fp, floc, fromp, fstr);
                if (c != '%') goto done;
                else _vl_vsss_advance(fp, floc);
                break;
            }
            default: {
                // Deal with all read-and-scan somethings
                // Note LSBs are preserved if there's an overflow
                const int obits = va_arg(ap, int);
                WData qowp[2] = {0, 0};
                WDataOutP owp = qowp;
                if (obits > VL_QUADSIZE) {
                    owp = va_arg(ap, WDataOutP);
                }
                for (int i=0; i<VL_WORDS_I(obits); ++i) owp[i] = 0;
                switch (fmt) {
                case 'c': {
                    int c = _vl_vsss_peek(fp, floc, fromp, fstr);
                    if (c==EOF) goto done;
                    else _vl_vsss_advance(fp, floc);
                    owp[0] = c;
                    break;
                }
                case 's': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, NULL);
                    if (!tmp[0]) goto done;
                    int lpos = (static_cast<int>(strlen(tmp)))-1;
                    int lsb = 0;
                    for (int i=0; i<obits && lpos>=0; --lpos) {
                        _vl_vsss_setbit(owp, obits, lsb, 8, tmp[lpos]); lsb+=8;
                    }
                    break;
                }
                case 'd': {  // Signed decimal
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, "0123456789+-xXzZ?_");
                    if (!tmp[0]) goto done;
                    vlsint64_t ld;
                    sscanf(tmp, "%30" VL_PRI64 "d",&ld);
                    VL_SET_WQ(owp, ld);
                    break;
                }
                case 'f':
                case 'e':
                case 'g': {  // Real number
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, "+-.0123456789eE");
                    if (!tmp[0]) goto done;
                    // cppcheck-suppress unusedStructMember  // It's used
                    union { double r; vlsint64_t ld; } u;
                    u.r = strtod(tmp, NULL);
                    VL_SET_WQ(owp, u.ld);
                    break;
                }
                case 't':  // FALLTHRU  // Time
                case '#': {  // Unsigned decimal
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, "0123456789+-xXzZ?_");
                    if (!tmp[0]) goto done;
                    QData ld;
                    sscanf(tmp, "%30" VL_PRI64 "u",&ld);
                    VL_SET_WQ(owp, ld);
                    break;
                }
                case 'b': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, "01xXzZ?_");
                    if (!tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 1, tmp, 0, strlen(tmp));
                    break;
                }
                case 'o': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, "01234567xXzZ?_");
                    if (!tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 3, tmp, 0, strlen(tmp));
                    break;
                }
                case 'x': {
                    _vl_vsss_skipspace(fp, floc, fromp, fstr);
                    _vl_vsss_read(fp, floc, fromp, fstr, tmp, "0123456789abcdefABCDEFxXzZ?_");
                    if (!tmp[0]) goto done;
                    _vl_vsss_based(owp, obits, 4, tmp, 0, strlen(tmp));
                    break;
                }
                default:
                    std::string msg = std::string("Unknown _vl_vsscanf code: ")+pos[0];
                    VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
                    break;
                }  // switch

                got++;
                // Reload data if non-wide (if wide, we put it in the right place directly)
                if (obits <= VL_BYTESIZE) {
                    CData* p = va_arg(ap, CData*); *p = owp[0];
                } else if (obits <= VL_SHORTSIZE) {
                    SData* p = va_arg(ap, SData*); *p = owp[0];
                } else if (obits <= VL_WORDSIZE) {
                    IData* p = va_arg(ap, IData*); *p = owp[0];
                } else if (obits <= VL_QUADSIZE) {
                    QData* p = va_arg(ap, QData*); *p = VL_SET_QW(owp);
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
    return VerilatedImp::fdToFp(lhs);
}

void _VL_VINT_TO_STRING(int obits, char* destoutp, WDataInP sourcep) VL_MT_SAFE {
    // See also VL_DATA_TO_STRING_NW
    int lsb=obits-1;
    bool start=true;
    char* destp = destoutp;
    for (; lsb>=0; --lsb) {
        lsb = (lsb / 8) * 8;  // Next digit
        IData charval = VL_BITRSHIFT_W(sourcep, lsb) & 0xff;
        if (!start || charval) {
            *destp++ = (charval==0)?' ':charval;
            start = false;  // Drop leading 0s
        }
    }
    *destp = '\0';  // Terminate
    // Drop trailing spaces
    if (!start) while (isspace(*(destp-1)) && destp>destoutp) *--destp = '\0';
}

void _VL_STRING_TO_VINT(int obits, void* destp, size_t srclen, const char* srcp) VL_MT_SAFE {
    // Convert C string to Verilog format
    size_t bytes = VL_BYTES_I(obits);
    char* op = reinterpret_cast<char*>(destp);
    if (srclen > bytes) srclen = bytes;  // Don't overflow destination
    size_t i;
    for (i=0; i<srclen; ++i) { *op++ = srcp[srclen-1-i]; }
    for (; i<bytes; ++i) { *op++ = 0; }
}

IData VL_FGETS_IXI(int obits, void* destp, IData fpi) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;

    // The string needs to be padded with 0's in unused spaces in front of
    // any read data.  This means we can't know in what location the first
    // character will finally live, so we need to copy.  Yuk.
    IData bytes = VL_BYTES_I(obits);
    char buffer[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    // V3Emit has static check that bytes < VL_TO_STRING_MAX_WORDS, but be safe
    if (VL_UNLIKELY(bytes > VL_TO_STRING_MAX_WORDS*VL_WORDSIZE)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: fgets buffer overrun");
    }

    // We don't use fgets, as we must read \0s.
    IData got = 0;
    char* cp = buffer;
    while (got < bytes) {
        int c = getc(fp);  // getc() is threadsafe
        if (c==EOF) break;
        *cp++ = c;  got++;
        if (c=='\n') break;
    }

    _VL_STRING_TO_VINT(obits, destp, got, buffer);
    return got;
}

IData VL_FOPEN_NI(const std::string& filename, IData mode) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    char modez[5];
    _VL_VINT_TO_STRING(VL_WORDSIZE, modez, &mode);
    return VL_FOPEN_S(filename.c_str(), modez);
}
IData VL_FOPEN_QI(QData filename, IData mode) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    WData fnw[2];  VL_SET_WQ(fnw, filename);
    return VL_FOPEN_WI(2, fnw, mode);
}
IData VL_FOPEN_WI(int fnwords, WDataInP filenamep, IData mode) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(fnwords*VL_WORDSIZE, filenamez, filenamep);
    char modez[5];
    _VL_VINT_TO_STRING(VL_WORDSIZE, modez, &mode);
    return VL_FOPEN_S(filenamez, modez);
}
IData VL_FOPEN_S(const char* filenamep, const char* modep) VL_MT_SAFE {
    return VerilatedImp::fdNew(fopen(filenamep, modep));
}

void VL_FCLOSE_I(IData fdi) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fdi);
    if (VL_UNLIKELY(!fp)) return;
    fclose(fp);
    VerilatedImp::fdDelete(fdi);
}

void VL_SFORMAT_X(int obits, CData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, SData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, IData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, QData& destr, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, &destr, output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits, void* destp, const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    _VL_STRING_TO_VINT(obits, destp, output.length(), output.c_str());
}

void VL_SFORMAT_X(int obits_ignored, std::string &output, const char* formatp, ...) VL_MT_SAFE {
    if (obits_ignored) {}
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);
}

std::string VL_SFORMATF_NX(const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    return output;
}

void VL_WRITEF(const char* formatp, ...) VL_MT_SAFE {
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    VL_PRINTF_MT("%s", output.c_str());
}

void VL_FWRITEF(IData fpi, const char* formatp, ...) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    static VL_THREAD_LOCAL std::string output;  // static only for speed
    output = "";
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return;

    va_list ap;
    va_start(ap, formatp);
    _vl_vsformat(output, formatp, ap);
    va_end(ap);

    fputs(output.c_str(), fp);
}

IData VL_FSCANF_IX(IData fpi, const char* formatp, ...) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;

    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(fp, 0, NULL, "", formatp, ap);
    va_end(ap);
    return got;
}

IData VL_SSCANF_IIX(int lbits, IData ld, const char* formatp, ...) VL_MT_SAFE {
    WData fnw[2];  VL_SET_WI(fnw, ld);

    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(NULL, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IQX(int lbits, QData ld, const char* formatp, ...) VL_MT_SAFE {
    WData fnw[2];  VL_SET_WQ(fnw, ld);

    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(NULL, lbits, fnw, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_IWX(int lbits, WDataInP lwp, const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(NULL, lbits, lwp, "", formatp, ap);
    va_end(ap);
    return got;
}
IData VL_SSCANF_INX(int, const std::string& ld, const char* formatp, ...) VL_MT_SAFE {
    va_list ap;
    va_start(ap, formatp);
    IData got = _vl_vsscanf(NULL, ld.length()*8, NULL, ld, formatp, ap);
    va_end(ap);
    return got;
}

void VL_WRITEMEM_Q(bool hex, int width, int depth, int array_lsb, int,
                   QData filename, const void* memp, IData start,
                   IData end) VL_MT_SAFE {
    WData fnw[2];  VL_SET_WQ(fnw, filename);
    return VL_WRITEMEM_W(hex, width, depth, array_lsb,2, fnw, memp, start, end);
}

void VL_WRITEMEM_W(bool hex, int width, int depth, int array_lsb, int fnwords,
                   WDataInP filenamep, const void* memp, IData start,
                   IData end) VL_MT_SAFE {
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(fnwords*VL_WORDSIZE, filenamez, filenamep);
    std::string filenames(filenamez);
    return VL_WRITEMEM_N(hex, width, depth, array_lsb, filenames, memp, start, end);
}

const char* memhFormat(int nBits) {
    assert((nBits >= 1) && (nBits <= 32));

    static char buf[32];
    switch ((nBits - 1) / 4) {
    case 0: VL_SNPRINTF(buf, 32, "%%01x"); break;
    case 1: VL_SNPRINTF(buf, 32, "%%02x"); break;
    case 2: VL_SNPRINTF(buf, 32, "%%03x"); break;
    case 3: VL_SNPRINTF(buf, 32, "%%04x"); break;
    case 4: VL_SNPRINTF(buf, 32, "%%05x"); break;
    case 5: VL_SNPRINTF(buf, 32, "%%06x"); break;
    case 6: VL_SNPRINTF(buf, 32, "%%07x"); break;
    case 7: VL_SNPRINTF(buf, 32, "%%08x"); break;
    default: assert(false); break;
    }
    return buf;
}

void VL_WRITEMEM_N(
    bool hex,  // Hex format, else binary
    int width,  // Width of each array row
    int depth,  // Number of rows
    int array_lsb,  // Index of first row. Valid row addresses
    //              //  range from array_lsb up to (array_lsb + depth - 1)
    const std::string& filename,  // Output file name
    const void* memp,  // Array state
    IData start,  // First array row address to write
    IData end  // Last address to write
    ) VL_MT_SAFE {
    if (VL_UNLIKELY(!hex)) {
        VL_FATAL_MT(filename.c_str(), 0, "",
                    "VL_WRITEMEM_N only supports hex format for now, sorry!");
        return;
    }
    FILE* fp = fopen(filename.c_str(), "w");
    if (VL_UNLIKELY(!fp)) {
        VL_FATAL_MT(filename.c_str(), 0, "", "$writemem file not found");
        return;
    }

    for (int row_addr = start; row_addr <= end; ++row_addr) {
        if ((row_addr < array_lsb)
            || (row_addr > array_lsb + depth - 1)) {
            vluint32_t endmax = ~0;
            if (end != endmax) {
                VL_FATAL_MT(filename.c_str(), 0, "",
                            "$writemem specified address out-of-bounds");
            }
            // else, it's not an error to overflow due to end == endmax,
            // just return cleanly.
            goto cleanup;
        }

        // Compute the offset into the memp array.
        int row_offset = row_addr - array_lsb;

        if (width <= 8) {
            const CData* datap
                = &(reinterpret_cast<const CData*>(memp))[row_offset];
            fprintf(fp, memhFormat(width), VL_MASK_I(width) & *datap);
            fprintf(fp, "\n");
        } else if (width <= 16) {
            const SData* datap
                = &(reinterpret_cast<const SData*>(memp))[row_offset];
            fprintf(fp, memhFormat(width), VL_MASK_I(width) & *datap);
            fprintf(fp, "\n");
        } else if (width <= 32) {
            const IData* datap
                = &(reinterpret_cast<const IData*>(memp))[row_offset];
            fprintf(fp, memhFormat(width), VL_MASK_I(width) & *datap);
            fprintf(fp, "\n");
        } else if (width <= 64) {
            const QData* datap
                = &(reinterpret_cast<const QData*>(memp))[row_offset];
            vluint64_t value = VL_MASK_Q(width) & *datap;
            vluint32_t lo = value & 0xffffffff;
            vluint32_t hi = value >> 32;
            fprintf(fp, memhFormat(width - 32), hi);
            fprintf(fp, "%08x\n", lo);
        } else {
            WDataInP memDatap = reinterpret_cast<WDataInP>(memp);
            WDataInP datap = &memDatap[row_offset * VL_WORDS_I(width)];
            // output as a sequence of VL_WORDSIZE'd words
            // from MSB to LSB. Mask off the MSB word which could
            // contain junk above the top of valid data.
            int word_idx = ((width - 1) / VL_WORDSIZE);
            bool first = true;
            while (word_idx >= 0) {
                IData data = datap[word_idx];
                if (first) {
                    data &= VL_MASK_I(width);
                    int top_word_nbits = ((width - 1) & 0x1f) + 1;
                    fprintf(fp, memhFormat(top_word_nbits), data);
                } else {
                    fprintf(fp, "%08x", data);
                }

                word_idx--;
                first = false;
            }
            fprintf(fp, "\n");
        }
    }

  cleanup:
    fclose(fp);
}

IData VL_FREAD_I(int width, int array_lsb, int array_size,
                 void* memp, IData fpi, IData start, IData count) VL_MT_SAFE {
    // While threadsafe, each thread can only access different file handles
    FILE* fp = VL_CVT_I_FP(fpi);
    if (VL_UNLIKELY(!fp)) return 0;
    if (count > (array_size - (start - array_lsb))) count = array_size - (start - array_lsb);
    // Prep for reading
    IData read_count = 0;
    IData read_elements = 0;
    int start_shift = (width-1) & ~7;  // bit+7:bit gets first character
    int shift = start_shift;
    // Read the data
    // We process a character at a time, as then we don't need to deal
    // with changing buffer sizes dynamically, etc.
    while (1) {
        int c = fgetc(fp);
        if (VL_UNLIKELY(c==EOF)) break;
        // Shift value in
        IData entry = read_elements + start - array_lsb;
        if (width <= 8) {
            CData* datap = &(reinterpret_cast<CData*>(memp))[entry];
            if (shift == start_shift) { *datap = 0; }
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= 16) {
            SData* datap = &(reinterpret_cast<SData*>(memp))[entry];
            if (shift == start_shift) { *datap = 0; }
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= VL_WORDSIZE) {
            IData* datap = &(reinterpret_cast<IData*>(memp))[entry];
            if (shift == start_shift) { *datap = 0; }
            *datap |= (c << shift) & VL_MASK_I(width);
        } else if (width <= VL_QUADSIZE) {
            QData* datap = &(reinterpret_cast<QData*>(memp))[entry];
            if (shift == start_shift) { *datap = 0; }
            *datap |= ((static_cast<QData>(c) << static_cast<QData>(shift))
                       & VL_MASK_Q(width));
            } else {
            WDataOutP datap = &(reinterpret_cast<WDataOutP>(memp))[ entry*VL_WORDS_I(width) ];
            if (shift == start_shift) { VL_ZERO_RESET_W(width, datap); }
            datap[VL_BITWORD_I(shift)] |= (c << VL_BITBIT_I(shift));
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

void VL_READMEM_Q(bool hex, int width, int depth, int array_lsb, int,
                  QData filename, void* memp, IData start, IData end) VL_MT_SAFE {
    WData fnw[2];  VL_SET_WQ(fnw, filename);
    return VL_READMEM_W(hex, width, depth, array_lsb, 2, fnw, memp, start, end);
}

void VL_READMEM_W(bool hex, int width, int depth, int array_lsb, int fnwords,
                  WDataInP filenamep, void* memp, IData start, IData end) VL_MT_SAFE {
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(fnwords*VL_WORDSIZE, filenamez, filenamep);
    std::string filenames(filenamez);
    return VL_READMEM_N(hex, width, depth, array_lsb, filenames, memp, start, end);
}

void VL_READMEM_N(
    bool hex,  // Hex format, else binary
    int width,  // Width of each array row
    int depth,  // Number of rows
    int array_lsb,  // Index of first row. Valid row addresses
    //              //  range from array_lsb up to (array_lsb + depth - 1)
    const std::string& filename,  // Input file name
    void* memp,  // Array state
    IData start,  // First array row address to read
    IData end  // Last row address to read
    ) VL_MT_SAFE {
    FILE* fp = fopen(filename.c_str(), "r");
    if (VL_UNLIKELY(!fp)) {
        // We don't report the Verilog source filename as it slow to have to pass it down
        VL_FATAL_MT(filename.c_str(), 0, "", "$readmem file not found");
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
        if (VL_UNLIKELY(c==EOF)) break;
        //printf("%d: Got '%c' Addr%x IN%d IgE%d IgC%d ninc%d\n",
        //       linenum, c, addr, innum, ignore_to_eol, ignore_to_cmt, needinc);
        if (c=='\n') { linenum++; ignore_to_eol=false; if (innum) reading_addr=false; innum=false; }
        else if (c=='\t' || c==' ' || c=='\r' || c=='\f') { if (innum) reading_addr=false; innum=false; }
        // Skip // comments and detect /* comments
        else if (ignore_to_cmt && lastc=='*' && c=='/') {
            ignore_to_cmt = false; if (innum) reading_addr=false; innum=false;
        } else if (!ignore_to_eol && !ignore_to_cmt) {
            if (lastc=='/' && c=='*') { ignore_to_cmt = true; }
            else if (lastc=='/' && c=='/') { ignore_to_eol = true; }
            else if (c=='/') {}  // Part of /* or //
            else if (c=='#') { ignore_to_eol = true; }
            else if (c=='_') {}
            else if (c=='@') { reading_addr = true; innum=false; needinc=false; }
            // Check for hex or binary digits as file format requests
            else if (isxdigit(c) || (!reading_addr && (c=='x' || c=='X'))) {
                c = tolower(c);
                int value = (c >= 'a' ? (c=='x' ? VL_RAND_RESET_I(4) : (c-'a'+10)) : (c-'0'));
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
                    if (VL_UNLIKELY(addr >= static_cast<IData>(depth+array_lsb)
                                    || addr < static_cast<IData>(array_lsb))) {
                        VL_FATAL_MT(filename.c_str(), linenum, "",
                                    "$readmem file address beyond bounds of array");
                    } else {
                        int entry = addr - array_lsb;
                        QData shift = hex ? VL_ULL(4) : VL_ULL(1);
                        // Shift value in
                        if (width<=8) {
                            CData* datap = &(reinterpret_cast<CData*>(memp))[entry];
                            if (!innum) { *datap = 0; }
                            *datap = ((*datap << shift) + value) & VL_MASK_I(width);
                        } else if (width<=16) {
                            SData* datap = &(reinterpret_cast<SData*>(memp))[entry];
                            if (!innum) { *datap = 0; }
                            *datap = ((*datap << shift) + value) & VL_MASK_I(width);
                        } else if (width<=VL_WORDSIZE) {
                            IData* datap = &(reinterpret_cast<IData*>(memp))[entry];
                            if (!innum) { *datap = 0; }
                            *datap = ((*datap << shift) + value) & VL_MASK_I(width);
                        } else if (width<=VL_QUADSIZE) {
                            QData* datap = &(reinterpret_cast<QData*>(memp))[entry];
                            if (!innum) { *datap = 0; }
                            *datap = ((*datap << static_cast<QData>(shift))
                                      + static_cast<QData>(value)) & VL_MASK_Q(width);
                        } else {
                            WDataOutP datap = &(reinterpret_cast<WDataOutP>(memp))[ entry*VL_WORDS_I(width) ];
                            if (!innum) { VL_ZERO_RESET_W(width, datap); }
                            _VL_SHIFTL_INPLACE_W(width, datap, static_cast<IData>(shift));
                            datap[0] |= value;
                        }
                        if (VL_UNLIKELY(value>=(1<<shift))) {
                            VL_FATAL_MT(filename.c_str(), linenum, "",
                                        "$readmemb (binary) file contains hex characters");
                        }
                    }
                }
                innum = true;
            }
            else {
                VL_FATAL_MT(filename.c_str(), linenum, "", "$readmem file syntax error");
            }
        }
        lastc = c;
    }
    if (needinc) { addr++; }

    // Final checks
    fclose(fp);
    if (VL_UNLIKELY(end != VL_UL(0xffffffff) && addr != (end+1))) {
        VL_FATAL_MT(filename.c_str(), linenum, "",
                    "$readmem file ended before specified ending-address");
    }
}

IData VL_SYSTEM_IQ(QData lhs) VL_MT_SAFE {
    WData lhsw[2];  VL_SET_WQ(lhsw, lhs);
    return VL_SYSTEM_IW(2, lhsw);
}
IData VL_SYSTEM_IW(int lhswords, WDataInP lhsp) VL_MT_SAFE {
    char filenamez[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    _VL_VINT_TO_STRING(lhswords*VL_WORDSIZE, filenamez, lhsp);
    int code = system(filenamez);  // Yes, system() is threadsafe
    return code >> 8;  // Want exit status
}

IData VL_TESTPLUSARGS_I(const char* formatp) VL_MT_SAFE {
    const std::string& match = VerilatedImp::argPlusMatch(formatp);
    if (match.empty()) return 0;
    else return 1;
}

IData VL_VALUEPLUSARGS_INW(int rbits, const std::string& ld, WDataOutP rwp) VL_MT_SAFE {
    std::string prefix;
    bool inPct = false;
    bool done = false;
    char fmt = ' ';
    for (const char* posp = ld.c_str(); !done && *posp; ++posp) {
        if (!inPct && posp[0]=='%') {
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
    case 'd':
        vlsint64_t lld;
        sscanf(dp, "%30" VL_PRI64 "d",&lld);
        VL_SET_WQ(rwp, lld);
        break;
    case 'b':
        _vl_vsss_based(rwp, rbits, 1, dp, 0, strlen(dp));
        break;
    case 'o':
        _vl_vsss_based(rwp, rbits, 3, dp, 0, strlen(dp));
        break;
    case 'h':  // FALLTHRU
    case 'x':
        _vl_vsss_based(rwp, rbits, 4, dp, 0, strlen(dp));
        break;
    case 's':  // string/no conversion
        for (int i=0, lsb=0, posp=static_cast<int>(strlen(dp))-1; i<rbits && posp>=0; --posp) {
            _vl_vsss_setbit(rwp, rbits, lsb, 8, dp[posp]); lsb+=8;
        }
        break;
    case 'e':  // FALLTHRU - Unsupported
    case 'f':  // FALLTHRU - Unsupported
    case 'g':  // FALLTHRU - Unsupported
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
        if (!inPct && posp[0]=='%') {
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
    static VL_THREAD_LOCAL char outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match.empty()) return NULL;
    strncpy(outstr, match.c_str()+strlen(prefixp)+1,  // +1 to skip the "+"
            VL_VALUE_STRING_MAX_WIDTH);
    outstr[VL_VALUE_STRING_MAX_WIDTH-1] = '\0';
    return outstr;
}

//===========================================================================
// Heavy functions

std::string VL_CVT_PACK_STR_NW(int lwords, WDataInP lwp) VL_MT_SAFE {
    // See also _VL_VINT_TO_STRING
    char destout[VL_TO_STRING_MAX_WORDS*VL_WORDSIZE+1];
    int obits = lwords * VL_WORDSIZE;
    int lsb=obits-1;
    bool start=true;
    char* destp = destout;
    int len = 0;
    for (; lsb>=0; --lsb) {
        lsb = (lsb / 8) * 8;  // Next digit
        IData charval = VL_BITRSHIFT_W(lwp, lsb) & 0xff;
        if (!start || charval) {
            *destp++ = (charval==0)?' ':charval;
            len++;
            start = false;  // Drop leading 0s
        }
    }
    return std::string(destout, len);
}

//===========================================================================
// Verilated:: Methods

Verilated::ThreadLocal::ThreadLocal()
    :
#ifdef VL_THREADED
    t_mtaskId(0),
    t_endOfEvalReqd(0),
#endif
    t_dpiScopep(NULL), t_dpiFilename(0), t_dpiLineno(0) {
}
Verilated::ThreadLocal::~ThreadLocal() {
}

void Verilated::debug(int level) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_debug = level;
    if (level) {
#ifdef VL_DEBUG
        VL_DEBUG_IF(VL_DBG_MSGF("- Verilated::debug is on. Message prefix indicates {<thread>,<sequence_number>}.\n"););
#else
        VL_PRINTF_MT("- Verilated::debug attempted, but compiled without VL_DEBUG, so messages suppressed.\n");
#endif
    }
}
void Verilated::randReset(int val) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_randReset = val;
}
void Verilated::randSeed(int val) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_randSeed = val;
}
void Verilated::calcUnusedSigs(bool flag) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_calcUnusedSigs = flag;
}
void Verilated::gotFinish(bool flag) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_gotFinish = flag;
}
void Verilated::assertOn(bool flag) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_assertOn = flag;
}
void Verilated::fatalOnVpiError(bool flag) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_s.s_fatalOnVpiError = flag;
}
void Verilated::profThreadsStart(vluint64_t flag) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_ns.s_profThreadsStart = flag;
}
void Verilated::profThreadsWindow(vluint64_t flag) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    s_ns.s_profThreadsWindow = flag;
}
void Verilated::profThreadsFilenamep(const char* flagp) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    if (s_ns.s_profThreadsFilenamep) free(const_cast<char*>(s_ns.s_profThreadsFilenamep));
    s_ns.s_profThreadsFilenamep = strdup(flagp);
}


const char* Verilated::catName(const char* n1, const char* n2) VL_MT_SAFE {
    // Returns new'ed data
    // Used by symbol table creation to make module names
    static VL_THREAD_LOCAL char* strp = NULL;
    static VL_THREAD_LOCAL size_t len  = 0;
    size_t newlen = strlen(n1)+strlen(n2)+2;
    if (!strp || newlen > len) {
        if (strp) delete [] strp;
        strp = new char[newlen];
        len = newlen;
    }
    strcpy(strp, n1);
    if (*n1) strcat(strp, ".");
    strcat(strp, n2);
    return strp;
}

void Verilated::flushCb(VerilatedVoidCb cb) VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    if (s_flushCb == cb) {}  // Ok - don't duplicate
    else if (!s_flushCb) { s_flushCb=cb; }
    else {
        // Someday we may allow multiple callbacks ala atexit(), but until then
        VL_FATAL_MT("unknown", 0, "",
                    "Verilated::flushCb called twice with different callbacks");
    }
}

void Verilated::flushCall() VL_MT_SAFE {
    VerilatedLockGuard lock(m_mutex);
    if (s_flushCb) (*s_flushCb)();
    fflush(stderr);
    fflush(stdout);
}

const char* Verilated::productName() VL_PURE {
    return VERILATOR_PRODUCT;
}
const char* Verilated::productVersion() VL_PURE {
    return VERILATOR_VERSION;
}

void Verilated::commandArgs(int argc, const char** argv) VL_MT_SAFE {
    VerilatedLockGuard lock(s_args.m_argMutex);
    s_args.argc = argc;
    s_args.argv = argv;
    VerilatedImp::commandArgs(argc, argv);
}

const char* Verilated::commandArgsPlusMatch(const char* prefixp) VL_MT_SAFE {
    const std::string& match = VerilatedImp::argPlusMatch(prefixp);
    static VL_THREAD_LOCAL char outstr[VL_VALUE_STRING_MAX_WIDTH];
    if (match.empty()) return "";
    strncpy(outstr, match.c_str(), VL_VALUE_STRING_MAX_WIDTH);
    outstr[VL_VALUE_STRING_MAX_WIDTH-1] = '\0';
    return outstr;
}

void Verilated::overWidthError(const char* signame) VL_MT_SAFE {
    // Slowpath - Called only when signal sets too high of a bit
    std::string msg = (std::string("Testbench C set input '")
                       + signame
                       + "' to value that overflows what the signal's width can fit");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
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

void Verilated::internalsDump() VL_MT_SAFE {
    VerilatedImp::internalsDump();
}

void Verilated::scopesDump() VL_MT_SAFE {
    VerilatedImp::scopesDump();
}

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

void Verilated::endOfEvalGuts(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
    VL_DEBUG_IF(VL_DBG_MSGF("End-of-eval cleanup\n"););
    evalMsgQp->process();
}
#endif

//===========================================================================
// VerilatedImp:: Methods

void VerilatedImp::internalsDump() VL_MT_SAFE {
    VerilatedLockGuard lock(s_s.m_argMutex);
    VL_PRINTF_MT("internalsDump:\n");
    versionDump();
    VL_PRINTF_MT("  Argv:");
    for (ArgVec::const_iterator it=s_s.m_argVec.begin(); it!=s_s.m_argVec.end(); ++it) {
        VL_PRINTF_MT(" %s", it->c_str());
    }
    VL_PRINTF_MT("\n");
    scopesDump();
    exportsDump();
    userDump();
}
void VerilatedImp::versionDump() VL_MT_SAFE {
    VL_PRINTF_MT("  Version: %s %s\n",
                 Verilated::productName(), Verilated::productVersion());
}

void VerilatedImp::commandArgs(int argc, const char** argv) VL_EXCLUDES(s_s.m_argMutex) {
    VerilatedLockGuard lock(s_s.m_argMutex);
    s_s.m_argVec.clear();  // Always clear
    commandArgsAddGuts(argc, argv);
}
void VerilatedImp::commandArgsAdd(int argc, const char** argv) VL_EXCLUDES(s_s.m_argMutex) {
    VerilatedLockGuard lock(s_s.m_argMutex);
    commandArgsAddGuts(argc, argv);
}
void VerilatedImp::commandArgsAddGuts(int argc, const char** argv) VL_REQUIRES(s_s.m_argMutex) {
    if (!s_s.m_argVecLoaded) s_s.m_argVec.clear();
    for (int i=0; i<argc; ++i) {
        s_s.m_argVec.push_back(argv[i]);
        commandArgVl(argv[i]);
    }
    s_s.m_argVecLoaded = true;  // Can't just test later for empty vector, no arguments is ok
}
void VerilatedImp::commandArgVl(const std::string& arg) {
    if (0 == strncmp(arg.c_str(), "+verilator+", strlen("+verilator+"))) {
        std::string value;
        if (0) {
        }
        else if (arg == "+verilator+debug") {
            Verilated::debug(4);
        }
        else if (commandArgVlValue(arg, "+verilator+debugi+", value/*ref*/)) {
            Verilated::debug(atoi(value.c_str()));
        }
        else if (arg == "+verilator+help") {
            versionDump();
            VL_PRINTF_MT("For help, please see 'verilator --help'\n");
            VL_FATAL_MT("COMMAND_LINE", 0, "", "Exiting due to command line argument (not an error)");
        }
        else if (commandArgVlValue(arg, "+verilator+prof+threads+start+", value/*ref*/)) {
            Verilated::profThreadsStart(atoll(value.c_str()));
        }
        else if (commandArgVlValue(arg, "+verilator+prof+threads+window+", value/*ref*/)) {
            Verilated::profThreadsWindow(atol(value.c_str()));
        }
        else if (commandArgVlValue(arg, "+verilator+prof+threads+file+", value/*ref*/)) {
            Verilated::profThreadsFilenamep(value.c_str());
        }
        else if (commandArgVlValue(arg, "+verilator+rand+reset+", value/*ref*/)) {
            Verilated::randReset(atoi(value.c_str()));
        }
        else if (commandArgVlValue(arg, "+verilator+seed+", value/*ref*/)) {
            Verilated::randSeed(atoi(value.c_str()));
        }
        else if (arg == "+verilator+V") {
            versionDump();  // Someday more info too
            VL_FATAL_MT("COMMAND_LINE", 0, "", "Exiting due to command line argument (not an error)");
        }
        else if (arg == "+verilator+version") {
            versionDump();
            VL_FATAL_MT("COMMAND_LINE", 0, "", "Exiting due to command line argument (not an error)");
        }
        else {
            VL_PRINTF_MT("%%Warning: Unknown +verilator runtime argument: '%s'\n", arg.c_str());
        }
    }
}
bool VerilatedImp::commandArgVlValue(const std::string& arg,
                                     const std::string& prefix, std::string& valuer) {
    size_t len = prefix.length();
    if (0==strncmp(prefix.c_str(), arg.c_str(), len)) {
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
    : m_namep(strdup(namep)) {
}

VerilatedModule::~VerilatedModule() {
    // Memory cleanup - not called during normal operation
    // NOLINTNEXTLINE(google-readability-casting)
    if (m_namep) { free((void*)(m_namep)); m_namep=NULL; }
}

//======================================================================
// VerilatedVar:: Methods

// cppcheck-suppress unusedFunction  // Used by applications
vluint32_t VerilatedVarProps::entSize() const {
    vluint32_t size = 1;
    switch (vltype()) {
    case VLVT_PTR:      size=sizeof(void*); break;
    case VLVT_UINT8:    size=sizeof(CData); break;
    case VLVT_UINT16:   size=sizeof(SData); break;
    case VLVT_UINT32:   size=sizeof(IData); break;
    case VLVT_UINT64:   size=sizeof(QData); break;
    case VLVT_WDATA:    size=VL_WORDS_I(packed().elements())*sizeof(IData); break;
    default:            size=0; break;
    }
    return size;
}

size_t VerilatedVarProps::totalSize() const {
    size_t size = entSize();
    for (int dim=1; dim<=dims(); ++dim) {
        size *= m_unpacked[dim].elements();
    }
    return size;
}

void* VerilatedVarProps::datapAdjustIndex(void* datap, int dim, int indx) const {
    if (VL_UNLIKELY(dim <=0 || dim > m_udims || dim > 3)) return NULL;
    if (VL_UNLIKELY(indx < low(dim) || indx > high(dim))) return NULL;
    int indxAdj = indx - low(dim);
    vluint8_t* bytep = reinterpret_cast<vluint8_t*>(datap);
    // If on index 1 of a 2 index array, then each index 1 is index2sz*entsz
    size_t slicesz = entSize();
    for (int d=dim+1; d<=m_udims; ++d) slicesz *= elements(d);
    bytep += indxAdj*slicesz;
    return bytep;
}

//======================================================================
// VerilatedScope:: Methods

VerilatedScope::VerilatedScope() {
    m_callbacksp = NULL;
    m_namep = NULL;
    m_funcnumMax = 0;
    m_symsp = NULL;
    m_varsp = NULL;
}

VerilatedScope::~VerilatedScope() {
    // Memory cleanup - not called during normal operation
    VerilatedImp::scopeErase(this);
    if (m_namep) { delete [] m_namep; m_namep = NULL; }
    if (m_callbacksp) { delete [] m_callbacksp; m_callbacksp = NULL; }
    if (m_varsp) { delete m_varsp; m_varsp = NULL; }
    m_funcnumMax = 0;  // Force callback table to empty
}

void VerilatedScope::configure(VerilatedSyms* symsp, const char* prefixp, const char* suffixp) VL_MT_UNSAFE {
    // Slowpath - called once/scope at construction
    // We don't want the space and reference-count access overhead of strings.
    m_symsp = symsp;
    char* namep = new char[strlen(prefixp)+strlen(suffixp)+2];
    strcpy(namep, prefixp);
    if (*prefixp && *suffixp) strcat(namep, ".");
    strcat(namep, suffixp);
    m_namep = namep;
    VerilatedImp::scopeInsert(this);
}

void VerilatedScope::exportInsert(int finalize, const char* namep, void* cb) VL_MT_UNSAFE {
    // Slowpath - called once/scope*export at construction
    // Insert a exported function into scope table
    int funcnum = VerilatedImp::exportInsert(namep);
    if (!finalize) {
        // Need two passes so we know array size to create
        // Alternative is to dynamically stretch the array, which is more code, and slower.
        if (funcnum >= m_funcnumMax) { m_funcnumMax = funcnum+1; }
    } else {
        if (VL_UNLIKELY(funcnum >= m_funcnumMax)) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "Internal: Bad funcnum vs. pre-finalize maximum");
        }
        if (VL_UNLIKELY(!m_callbacksp)) {  // First allocation
            m_callbacksp = new void* [m_funcnumMax];
            memset(m_callbacksp, 0, m_funcnumMax*sizeof(void*));
        }
        m_callbacksp[funcnum] = cb;
    }
}

void VerilatedScope::varInsert(int finalize, const char* namep, void* datap,
                               VerilatedVarType vltype, int vlflags, int dims, ...) VL_MT_UNSAFE {
    // Grab dimensions
    // In the future we may just create a large table at emit time and statically construct from that.
    if (!finalize) return;

    if (!m_varsp) m_varsp = new VerilatedVarNameMap();
    VerilatedVar var(namep, datap, vltype, static_cast<VerilatedVarFlags>(vlflags), dims);

    va_list ap;
    va_start(ap, dims);
    for (int i=0; i<dims; ++i) {
        int msb = va_arg(ap, int);
        int lsb = va_arg(ap, int);
        if (i==0) {
            var.m_packed.m_left = msb;
            var.m_packed.m_right = lsb;
        } else if (i>=1 && i<=3) {
            var.m_unpacked[i-1].m_left = msb;
            var.m_unpacked[i-1].m_right = lsb;
        } else {
            // We could have a linked list of ranges, but really this whole thing needs
            // to be generalized to support structs and unions, etc.
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        (std::string("Unsupported multi-dimensional public varInsert: ")
                         + namep).c_str());
        }
    }
    va_end(ap);

    m_varsp->insert(std::make_pair(namep, var));
}

// cppcheck-suppress unusedFunction  // Used by applications
VerilatedVar* VerilatedScope::varFind(const char* namep) const VL_MT_SAFE_POSTINIT {
    if (VL_LIKELY(m_varsp)) {
        VerilatedVarNameMap::iterator it = m_varsp->find(namep);
        if (VL_LIKELY(it != m_varsp->end())) {
            return &(it->second);
        }
    }
    return NULL;
}

void* VerilatedScope::exportFindNullError(int funcnum) VL_MT_SAFE {
    // Slowpath - Called only when find has failed
    std::string msg = (std::string("Testbench C called '")
                       +VerilatedImp::exportName(funcnum)
                       +"' but scope wasn't set, perhaps due to dpi import call without 'context'");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
    return NULL;
}

void* VerilatedScope::exportFindError(int funcnum) const {
    // Slowpath - Called only when find has failed
    std::string msg = (std::string("Testbench C called '")
                       +VerilatedImp::exportName(funcnum)
                       +"' but this DPI export function exists only in other scopes, not scope '"
                       +name()+"'");
    VL_FATAL_MT("unknown", 0, "", msg.c_str());
    return NULL;
}

void VerilatedScope::scopeDump() const {
    VL_PRINTF_MT("    SCOPE %p: %s\n", this, name());
    for (int i=0; i<m_funcnumMax; ++i) {
        if (m_callbacksp && m_callbacksp[i]) {
            VL_PRINTF_MT("       DPI-EXPORT %p: %s\n",
                         m_callbacksp[i], VerilatedImp::exportName(i));
        }
    }
    if (VerilatedVarNameMap* varsp = this->varsp()) {
        for (VerilatedVarNameMap::const_iterator it = varsp->begin();
             it != varsp->end(); ++it) {
            VL_PRINTF_MT("       VAR %p: %s\n", &(it->second), it->first);
        }
    }
}

//===========================================================================
// VerilatedOneThreaded:: Methods

#if defined(VL_THREADED) && defined(VL_DEBUG)
void VerilatedAssertOneThread::fatal_different() VL_MT_SAFE {
    VL_FATAL_MT(__FILE__, __LINE__, "", "Routine called that is single threaded, but called from"
                " a different thread then the expected constructing thread");
}
#endif

//===========================================================================
