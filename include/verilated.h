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
//*************************************************************************
///
/// \file
/// \brief Verilator: Common include for all Verilated C files
///
///     This file is included automatically by Verilator at the top of
///     all C++ files it generates.  It contains standard macros and
///     classes required by the Verilated code.
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_H_
#define _VERILATED_H_ 1  ///< Header Guard

#include "verilatedos.h"

#include <cassert>
#include <cmath>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
// <iostream> avoided to reduce compile time
// <map> avoided and instead in verilated_heavy.h to reduce compile time
// <string> avoided and instead in verilated_heavy.h to reduce compile time
#ifdef VL_THREADED
# include <atomic>
# include <mutex>
# include <thread>
#endif

//=============================================================================
// Switches

#if VM_TRACE  // Verilator tracing requested
# define WAVES 1  // Set backward compatibility flag
#endif

//=========================================================================
// Basic types

//                   P          // Packed data of bit type (C/S/I/Q/W)
typedef vluint8_t    CData;     ///< Verilated pack data, 1-8 bits
typedef vluint16_t   SData;     ///< Verilated pack data, 9-16 bits
typedef vluint32_t   IData;     ///< Verilated pack data, 17-32 bits
typedef vluint64_t   QData;     ///< Verilated pack data, 33-64 bits
typedef vluint32_t   WData;     ///< Verilated pack data, >64 bits, as an array
//      float        F          // No typedef needed; Verilator uses float
//      double       D          // No typedef needed; Verilator uses double
//      string       N          // No typedef needed; Verilator uses string

typedef const WData* WDataInP;  ///< Array input to a function
typedef WData* WDataOutP;  ///< Array output from a function

typedef void (*VerilatedVoidCb)(void);

class SpTraceVcd;
class SpTraceVcdCFile;
class VerilatedEvalMsgQueue;
class VerilatedScopeNameMap;
class VerilatedVar;
class VerilatedVarNameMap;
class VerilatedVcd;
class VerilatedVcdC;
class VerilatedFst;
class VerilatedFstC;

enum VerilatedVarType {
    VLVT_UNKNOWN=0,
    VLVT_PTR,           // Pointer to something
    VLVT_UINT8,         // AKA CData
    VLVT_UINT16,        // AKA SData
    VLVT_UINT32,        // AKA IData
    VLVT_UINT64,        // AKA QData
    VLVT_WDATA,         // AKA WData
    VLVT_STRING         // C++ string
};

enum VerilatedVarFlags {
    VLVD_0 = 0,         // None
    VLVD_IN = 1,        // == vpiInput
    VLVD_OUT = 2,       // == vpiOutput
    VLVD_INOUT = 3,     // == vpiInOut
    VLVD_NODIR = 5,     // == vpiNoDirection
    VLVF_MASK_DIR = 7,  // Bit mask for above directions
    // Flags
    VLVF_PUB_RD = (1<<8),  // Public readable
    VLVF_PUB_RW = (1<<9),  // Public writable
    VLVF_DPI_CLAY = (1<<10)  // DPI compatible C standard layout
};

//=========================================================================
/// Mutex and threading support

/// Return current thread ID (or 0), not super fast, cache if needed
extern vluint32_t VL_THREAD_ID() VL_MT_SAFE;

#if VL_THREADED

#define VL_LOCK_SPINS 50000  /// Number of times to spin for a mutex before relaxing

/// Mutex, wrapped to allow -fthread_safety checks
class VL_CAPABILITY("mutex") VerilatedMutex {
  private:
    std::mutex m_mutex;  // Mutex
  public:
    VerilatedMutex() {}
    ~VerilatedMutex() {}
    const VerilatedMutex& operator!() const { return *this; }  // For -fthread_safety
    /// Acquire/lock mutex
    void lock() VL_ACQUIRE() {
        // Try to acquire the lock by spinning.  If the wait is short,
        // avoids a trap to the OS plus OS scheduler overhead.
        if (VL_LIKELY(try_lock())) return;  // Short circuit loop
        for (int i = 0; i < VL_LOCK_SPINS; ++i) {
            if (VL_LIKELY(try_lock())) return;
            VL_CPU_RELAX();
        }
        // Spinning hasn't worked, pay the cost of blocking.
        m_mutex.lock();
    }
    /// Release/unlock mutex
    void unlock() VL_RELEASE() { m_mutex.unlock(); }
    /// Try to acquire mutex.  Returns true on success, and false on failure.
    bool try_lock() VL_TRY_ACQUIRE(true) { return m_mutex.try_lock(); }
};

/// Lock guard for mutex (ala std::lock_guard), wrapped to allow -fthread_safety checks
class VL_SCOPED_CAPABILITY VerilatedLockGuard {
    VL_UNCOPYABLE(VerilatedLockGuard);
  private:
    VerilatedMutex& m_mutexr;
  public:
    explicit VerilatedLockGuard(VerilatedMutex& mutexr) VL_ACQUIRE(mutexr)
        : m_mutexr(mutexr) {
        m_mutexr.lock();
    }
    ~VerilatedLockGuard() VL_RELEASE() {
        m_mutexr.unlock();
    }
};

#else  // !VL_THREADED

/// Empty non-threaded mutex to avoid #ifdefs in consuming code
class VerilatedMutex {
public:
    void lock() {}
    void unlock() {}
};

/// Empty non-threaded lock guard to avoid #ifdefs in consuming code
class VerilatedLockGuard {
    VL_UNCOPYABLE(VerilatedLockGuard);
public:
    explicit VerilatedLockGuard(VerilatedMutex&) {}
    ~VerilatedLockGuard() {}
};

#endif  // VL_THREADED

/// Remember the calling thread at construction time, and make sure later calls use same thread
class VerilatedAssertOneThread {
    // MEMBERS
#if defined(VL_THREADED) && defined(VL_DEBUG)
    vluint32_t m_threadid;  /// Thread that is legal
public:
    // CONSTRUCTORS
    /// The constructor establishes the thread id for all later calls.
    /// If necessary, a different class could be made that inits it otherwise.
    VerilatedAssertOneThread() : m_threadid(VL_THREAD_ID()) { }
    ~VerilatedAssertOneThread() { check(); }
    // METHODS
    /// Check that the current thread ID is the same as the construction thread ID
    void check() VL_MT_UNSAFE_ONE {
        if (!VL_LIKELY(m_threadid == VL_THREAD_ID())) {
            fatal_different();
        }
    }
    static void fatal_different() VL_MT_SAFE;
#else  // !VL_THREADED || !VL_DEBUG
public:
    void check() {}
#endif
};

//=========================================================================
/// Base class for all Verilated module classes

class VerilatedModule {
    VL_UNCOPYABLE(VerilatedModule);
private:
    const char* m_namep;  ///< Module name
public:
    explicit VerilatedModule(const char* namep);  ///< Create module with given hierarchy name
    ~VerilatedModule();
    const char* name() const { return m_namep; }  ///< Return name of module
};

//=========================================================================
// Declare nets

#ifndef VL_ST_SIG
# define VL_ST_SIG8(name, msb,lsb)      CData name              ///< Declare signal, 1-8 bits
# define VL_ST_SIG16(name, msb,lsb)     SData name              ///< Declare signal, 9-16 bits
# define VL_ST_SIG64(name, msb,lsb)     QData name              ///< Declare signal, 33-64 bits
# define VL_ST_SIG(name, msb,lsb)       IData name              ///< Declare signal, 17-32 bits
# define VL_ST_SIGW(name,msb,lsb,words) WData name[words]       ///< Declare signal, 65+ bits
#endif
#ifndef VL_SIG
# define VL_SIG8(name, msb,lsb)         CData name              ///< Declare signal, 1-8 bits
# define VL_SIG16(name, msb,lsb)        SData name              ///< Declare signal, 9-16 bits
# define VL_SIG64(name, msb,lsb)        QData name              ///< Declare signal, 33-64 bits
# define VL_SIG(name, msb,lsb)          IData name              ///< Declare signal, 17-32 bits
# define VL_SIGW(name, msb,lsb, words)  WData name[words]       ///< Declare signal, 65+ bits
# define VL_IN8(name, msb,lsb)          CData name              ///< Declare input signal, 1-8 bits
# define VL_IN16(name, msb,lsb)         SData name              ///< Declare input signal, 9-16 bits
# define VL_IN64(name, msb,lsb)         QData name              ///< Declare input signal, 33-64 bits
# define VL_IN(name, msb,lsb)           IData name              ///< Declare input signal, 17-32 bits
# define VL_INW(name, msb,lsb, words)   WData name[words]       ///< Declare input signal, 65+ bits
# define VL_INOUT8(name, msb,lsb)       CData name              ///< Declare bidir signal, 1-8 bits
# define VL_INOUT16(name, msb,lsb)      SData name              ///< Declare bidir signal, 9-16 bits
# define VL_INOUT64(name, msb,lsb)      QData name              ///< Declare bidir signal, 33-64 bits
# define VL_INOUT(name, msb,lsb)        IData name              ///< Declare bidir signal, 17-32 bits
# define VL_INOUTW(name, msb,lsb, words) WData name[words]      ///< Declare bidir signal, 65+ bits
# define VL_OUT8(name, msb,lsb)         CData name              ///< Declare output signal, 1-8 bits
# define VL_OUT16(name, msb,lsb)        SData name              ///< Declare output signal, 9-16 bits
# define VL_OUT64(name, msb,lsb)        QData name              ///< Declare output signal, 33-64bits
# define VL_OUT(name, msb,lsb)          IData name              ///< Declare output signal, 17-32 bits
# define VL_OUTW(name, msb,lsb, words)  WData name[words]       ///< Declare output signal, 65+ bits

# define VL_PIN_NOP(instname,pin,port)  ///< Connect a pin, ala SP_PIN
# define VL_CELL(instname,type)         ///< Declare a cell, ala SP_CELL

/// Declare a module, ala SC_MODULE
# define VL_MODULE(modname)             class modname : public VerilatedModule

/// Constructor, ala SC_CTOR
# define VL_CTOR(modname)               modname(const char* __VCname="")

/// Constructor declaration for C++, ala SP_CTOR_IMPL
# define VL_CTOR_IMP(modname)           modname::modname(const char* __VCname) : VerilatedModule(__VCname)

/// Constructor declaration for SystemC, ala SP_CTOR_IMPL
# define VL_SC_CTOR_IMP(modname)        modname::modname(sc_module_name)

#endif

//=========================================================================
// Functions overridable by user defines
// (Internals however must use VL_PRINTF_MT, which calls these.)

#ifndef VL_PRINTF
# define VL_PRINTF printf  ///< Print ala printf, called from main thread; may redefine if desired
#endif
#ifndef VL_VPRINTF
# define VL_VPRINTF vprintf  ///< Print ala vprintf, called from main thread; may redefine if desired
#endif

//===========================================================================
/// Verilator symbol table base class

class VerilatedSyms {
public:  // But for internal use only
#ifdef VL_THREADED
    VerilatedEvalMsgQueue* __Vm_evalMsgQp;
#endif
    VerilatedSyms();
    ~VerilatedSyms();
};

//===========================================================================
/// Verilator global class information class
/// This class is initialized by main thread only. Reading post-init is thread safe.

class VerilatedScope {
    // Fastpath:
    VerilatedSyms*      m_symsp;        ///< Symbol table
    void**              m_callbacksp;   ///< Callback table pointer (Fastpath)
    int                 m_funcnumMax;   ///< Maxium function number stored (Fastpath)
    // 4 bytes padding (on -m64), for rent.
    VerilatedVarNameMap* m_varsp;       ///< Variable map
    const char*         m_namep;        ///< Scope name (Slowpath)

public:  // But internals only - called from VerilatedModule's
    VerilatedScope();
    ~VerilatedScope();
    void configure(VerilatedSyms* symsp, const char* prefixp, const char* suffixp) VL_MT_UNSAFE;
    void exportInsert(int finalize, const char* namep, void* cb) VL_MT_UNSAFE;
    void varInsert(int finalize, const char* namep, void* datap,
                   VerilatedVarType vltype, int vlflags, int dims, ...) VL_MT_UNSAFE;
    // ACCESSORS
    const char* name() const { return m_namep; }
    inline VerilatedSyms* symsp() const { return m_symsp; }
    VerilatedVar* varFind(const char* namep) const VL_MT_SAFE_POSTINIT;
    VerilatedVarNameMap* varsp() const VL_MT_SAFE_POSTINIT { return m_varsp; }
    void scopeDump() const;
    void* exportFindError(int funcnum) const;
    static void* exportFindNullError(int funcnum) VL_MT_SAFE;
    static inline void* exportFind(const VerilatedScope* scopep, int funcnum) VL_MT_SAFE {
        if (VL_UNLIKELY(!scopep)) return exportFindNullError(funcnum);
        if (VL_LIKELY(funcnum < scopep->m_funcnumMax)) {
            // m_callbacksp must be declared, as Max'es are > 0
            return scopep->m_callbacksp[funcnum];
        } else {
            return scopep->exportFindError(funcnum);
        }
    }
};

//===========================================================================
/// Verilator global static information class

class Verilated {
    // MEMBERS
    // Slow path variables
    static VerilatedMutex m_mutex;  ///< Mutex for s_s/s_ns members, when VL_THREADED

    static VerilatedVoidCb  s_flushCb;  ///< Flush callback function

    static struct Serialized {  // All these members serialized/deserialized
        // Fast path
        int             s_debug;                ///< See accessors... only when VL_DEBUG set
        bool            s_calcUnusedSigs;       ///< Waves file on, need all signals calculated
        bool            s_gotFinish;            ///< A $finish statement executed
        bool            s_assertOn;             ///< Assertions are enabled
        bool            s_fatalOnVpiError;      ///< Stop on vpi error/unsupported
        // Slow path
        int s_randReset;  ///< Random reset: 0=all 0s, 1=all 1s, 2=random
        int s_randSeed;  ///< Random seed: 0=random
        Serialized();
        ~Serialized() {}
    } s_s;

    static struct NonSerialized {  // Non-serialized information
        // These are reloaded from on command-line settings, so do not need to persist
        // Fast path
        vluint64_t s_profThreadsStart;  ///< +prof+threads starting time
        vluint32_t s_profThreadsWindow;  ///< +prof+threads window size
        // Slow path
        const char* s_profThreadsFilenamep;  ///< +prof+threads filename
        NonSerialized();
        ~NonSerialized();
    } s_ns;

    // no need to be save-restored (serialized) the
    // assumption is that the restore is allowed to pass different arguments
    static struct CommandArgValues {
        VerilatedMutex m_argMutex;  ///< Mutex for s_args members, when VL_THREADED
        int argc;
        const char** argv;
        CommandArgValues() : argc(0), argv(NULL) {}
        ~CommandArgValues() {}
    } s_args;

    // Not covered by mutex, as per-thread
    static VL_THREAD_LOCAL struct ThreadLocal {
#ifdef VL_THREADED
        vluint32_t t_mtaskId;  ///< Current mtask# executing on this thread
        vluint32_t t_endOfEvalReqd;  ///< Messages may be pending, thread needs endOf-eval calls
#endif
        const VerilatedScope* t_dpiScopep;  ///< DPI context scope
        const char* t_dpiFilename;  ///< DPI context filename
        int t_dpiLineno;  ///< DPI context line number

        ThreadLocal();
        ~ThreadLocal();
    } t_s;

private:
    // CONSTRUCTORS
    VL_UNCOPYABLE(Verilated);

public:
    // METHODS - User called

    /// Select initial value of otherwise uninitialized signals.
    ////
    /// 0 = Set to zeros
    /// 1 = Set all bits to one
    /// 2 = Randomize all bits
    static void randReset(int val) VL_MT_SAFE;
    static int  randReset() VL_MT_SAFE { return s_s.s_randReset; }  ///< Return randReset value
    static void randSeed(int val) VL_MT_SAFE;
    static int  randSeed() VL_MT_SAFE { return s_s.s_randSeed; }  ///< Return randSeed value

    /// Enable debug of internal verilated code
    static void debug(int level) VL_MT_SAFE;
#ifdef VL_DEBUG
    /// Return debug level
    /// When multithreaded this may not immediately react to another thread changing the level (no mutex)
    static inline int debug() VL_MT_SAFE { return s_s.s_debug; }
#else
    static inline int debug() VL_PURE { return 0; }  ///< Return constant 0 debug level, so C++'s optimizer rips up
#endif
    /// Enable calculation of unused signals
    static void calcUnusedSigs(bool flag) VL_MT_SAFE;
    static bool calcUnusedSigs() VL_MT_SAFE {  ///< Return calcUnusedSigs value
        return s_s.s_calcUnusedSigs; }
    /// Did the simulation $finish?
    static void gotFinish(bool flag) VL_MT_SAFE;
    static bool gotFinish() VL_MT_SAFE { return s_s.s_gotFinish; }  ///< Return if got a $finish
    /// Allow traces to at some point be enabled (disables some optimizations)
    static void traceEverOn(bool flag) VL_MT_SAFE {
        if (flag) { calcUnusedSigs(flag); }
    }
    /// Enable/disable assertions
    static void assertOn(bool flag) VL_MT_SAFE;
    static bool assertOn() VL_MT_SAFE { return s_s.s_assertOn; }
    /// Enable/disable vpi fatal
    static void fatalOnVpiError(bool flag) VL_MT_SAFE;
    static bool fatalOnVpiError() VL_MT_SAFE { return s_s.s_fatalOnVpiError; }
    /// --prof-threads related settings
    static void profThreadsStart(vluint64_t flag) VL_MT_SAFE;
    static vluint64_t profThreadsStart() VL_MT_SAFE { return s_ns.s_profThreadsStart; }
    static void profThreadsWindow(vluint64_t flag) VL_MT_SAFE;
    static vluint32_t profThreadsWindow() VL_MT_SAFE { return s_ns.s_profThreadsWindow; }
    static void profThreadsFilenamep(const char* flagp) VL_MT_SAFE;
    static const char* profThreadsFilenamep() VL_MT_SAFE { return s_ns.s_profThreadsFilenamep; }

    /// Flush callback for VCD waves
    static void flushCb(VerilatedVoidCb cb) VL_MT_SAFE;
    static void flushCall() VL_MT_SAFE;

    /// Record command line arguments, for retrieval by $test$plusargs/$value$plusargs,
    /// and for parsing +verilator+ run-time arguments.
    /// This should be called before the first model is created.
    static void commandArgs(int argc, const char** argv) VL_MT_SAFE;
    static void commandArgs(int argc, char** argv) VL_MT_SAFE {
        commandArgs(argc, const_cast<const char**>(argv)); }
    static void commandArgsAdd(int argc, const char** argv);
    static CommandArgValues* getCommandArgs() VL_MT_SAFE { return &s_args; }
    /// Match plusargs with a given prefix. Returns static char* valid only for a single call
    static const char* commandArgsPlusMatch(const char* prefixp) VL_MT_SAFE;

    /// Produce name & version for (at least) VPI
    static const char* productName() VL_PURE;
    static const char* productVersion() VL_PURE;

    /// Convenience OS utilities
    static void mkdir(const char* dirname) VL_MT_UNSAFE;

    /// When multithreaded, quiesce the model to prepare for trace/saves/coverage
    /// This may only be called when no locks are held.
    static void quiesce() VL_MT_SAFE;

    /// For debugging, print much of the Verilator internal state.
    /// The output of this function may change in future
    /// releases - contact the authors before production use.
    static void internalsDump() VL_MT_SAFE;

    /// For debugging, print text list of all scope names with
    /// dpiImport/Export context.  This function may change in future
    /// releases - contact the authors before production use.
    static void scopesDump() VL_MT_SAFE;

public:
    // METHODS - INTERNAL USE ONLY (but public due to what uses it)
    // Internal: Create a new module name by concatenating two strings
    static const char* catName(const char* n1, const char* n2);  // Returns static data

    // Internal: Throw signal assertion
    static void overWidthError(const char* signame) VL_MT_SAFE;

    // Internal: Find scope
    static const VerilatedScope* scopeFind(const char* namep) VL_MT_SAFE;
    static const VerilatedScopeNameMap* scopeNameMap() VL_MT_SAFE;

    // Internal: Get and set DPI context
    static const VerilatedScope* dpiScope() VL_MT_SAFE { return t_s.t_dpiScopep; }
    static void dpiScope(const VerilatedScope* scopep) VL_MT_SAFE { t_s.t_dpiScopep = scopep; }
    static void dpiContext(const VerilatedScope* scopep, const char* filenamep, int lineno) VL_MT_SAFE {
        t_s.t_dpiScopep = scopep; t_s.t_dpiFilename = filenamep; t_s.t_dpiLineno = lineno; }
    static void dpiClearContext() VL_MT_SAFE { t_s.t_dpiScopep = NULL; }
    static bool dpiInContext() VL_MT_SAFE { return t_s.t_dpiScopep != NULL; }
    static const char* dpiFilenamep() VL_MT_SAFE { return t_s.t_dpiFilename; }
    static int dpiLineno() VL_MT_SAFE { return t_s.t_dpiLineno; }
    static int exportFuncNum(const char* namep) VL_MT_SAFE;

    static size_t serializedSize() VL_PURE { return sizeof(s_s); }
    static void* serializedPtr() VL_MT_UNSAFE { return &s_s; }  // Unsafe, for Serialize only
#ifdef VL_THREADED
    /// Set the mtaskId, called when an mtask starts
    static void mtaskId(vluint32_t id) VL_MT_SAFE { t_s.t_mtaskId = id; }
    static vluint32_t mtaskId() VL_MT_SAFE { return t_s.t_mtaskId; }
    static void endOfEvalReqdInc() VL_MT_SAFE { ++t_s.t_endOfEvalReqd; }
    static void endOfEvalReqdDec() VL_MT_SAFE { --t_s.t_endOfEvalReqd; }

    /// Called at end of each thread mtask, before finishing eval
    static void endOfThreadMTask(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
        if (VL_UNLIKELY(t_s.t_endOfEvalReqd)) { endOfThreadMTaskGuts(evalMsgQp); }
    }
    /// Called at end of eval loop
    static void endOfEval(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE {
        // It doesn't work to set endOfEvalReqd on the threadpool thread
        // and then check it on the eval thread since it's thread local.
        // It should be ok to call into endOfEvalGuts, it returns immediately
        // if there are no transactions.
        endOfEvalGuts(evalMsgQp);
    }
#endif

private:
#ifdef VL_THREADED
    static void endOfThreadMTaskGuts(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE;
    static void endOfEvalGuts(VerilatedEvalMsgQueue* evalMsgQp) VL_MT_SAFE;
#endif
};

//=========================================================================
// Extern functions -- User may override -- See verilated.cpp

/// Routine to call for $finish
/// User code may wish to replace this function, to do so, define VL_USER_FINISH.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_FINISH_MT instead, which eventually calls this.
extern void vl_finish(const char* filename, int linenum, const char* hier);

/// Routine to call for $stop
/// User code may wish to replace this function, to do so, define VL_USER_STOP.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_FINISH_MT instead, which eventually calls this.
extern void vl_stop(const char* filename, int linenum, const char* hier);

/// Routine to call for a couple of fatal messages
/// User code may wish to replace this function, to do so, define VL_USER_FATAL.
/// This code does not have to be thread safe.
/// Verilator internal code must call VL_FINISH_MT instead, which eventually calls this.
extern void vl_fatal(const char* filename, int linenum, const char* hier,
                     const char* msg);

//=========================================================================
// Extern functions -- Slow path

/// Multithread safe wrapper for calls to $finish
extern void VL_FINISH_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE;
/// Multithread safe wrapper for calls to $stop
extern void VL_STOP_MT(const char* filename, int linenum, const char* hier) VL_MT_SAFE;
/// Multithread safe wrapper to call for a couple of fatal messages
extern void VL_FATAL_MT(const char* filename, int linenum, const char* hier,
                        const char* msg) VL_MT_SAFE;

/// Print a string, multithread safe. Eventually VL_PRINTF will get called.
#ifdef VL_THREADED
extern void VL_PRINTF_MT(const char* formatp, ...) VL_ATTR_PRINTF(1) VL_MT_SAFE;
#else
# define VL_PRINTF_MT VL_PRINTF  // The following parens will take care of themselves
#endif
/// Print a debug message from internals with standard prefix, with printf style format
extern void VL_DBG_MSGF(const char* formatp, ...) VL_ATTR_PRINTF(1) VL_MT_SAFE;

extern IData VL_RANDOM_I(int obits);  ///< Randomize a signal
extern QData VL_RANDOM_Q(int obits);  ///< Randomize a signal
extern WDataOutP VL_RANDOM_W(int obits, WDataOutP outwp);  ///< Randomize a signal

/// Init time only, so slow is fine
extern IData VL_RAND_RESET_I(int obits);  ///< Random reset a signal
extern QData VL_RAND_RESET_Q(int obits);  ///< Random reset a signal
extern WDataOutP VL_RAND_RESET_W(int obits, WDataOutP outwp);  ///< Random reset a signal
extern WDataOutP VL_ZERO_RESET_W(int obits, WDataOutP outwp);  ///< Zero reset a signal (slow - else use VL_ZERO_W)

#if VL_THREADED
/// Return high-precision counter for profiling, or 0x0 if not available
inline QData VL_RDTSC_Q() { vluint64_t val; VL_RDTSC(val); return val; }
#endif

/// Math
extern WDataOutP _vl_moddiv_w(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp, bool is_modulus);

/// File I/O
extern IData VL_FGETS_IXI(int obits, void* destp, IData fpi);

extern IData VL_FOPEN_S(const char* filenamep, const char* modep);
extern IData VL_FOPEN_WI(int fnwords, WDataInP filenamep, IData mode);
extern IData VL_FOPEN_QI(QData filename, IData mode);
inline IData VL_FOPEN_II(IData filename, IData mode) VL_MT_SAFE {
    return VL_FOPEN_QI(filename, mode); }

extern void VL_FCLOSE_I(IData fdi);

extern IData VL_FREAD_I(int width, int array_lsb, int array_size,
                        void* memp, IData fpi, IData start, IData count);

extern void VL_READMEM_W(bool hex, int width, int depth, int array_lsb, int fnwords,
                         WDataInP filenamep, void* memp, IData start, IData end);
extern void VL_READMEM_Q(bool hex, int width, int depth, int array_lsb, int fnwords,
                         QData filename,     void* memp, IData start, IData end);
inline void VL_READMEM_I(bool hex, int width, int depth, int array_lsb, int fnwords,
                         IData filename,     void* memp, IData start, IData end) VL_MT_SAFE {
    VL_READMEM_Q(hex, width, depth, array_lsb, fnwords, filename, memp, start, end); }

extern void VL_WRITEMEM_W(bool hex, int width, int depth, int array_lsb, int fnwords,
                          WDataInP filenamep, const void* memp, IData start, IData end);
extern void VL_WRITEMEM_Q(bool hex, int width, int depth, int array_lsb, int fnwords,
                          QData filename,     const void* memp, IData start, IData end);
inline void VL_WRITEMEM_I(bool hex, int width, int depth, int array_lsb, int fnwords,
                          IData filename,     const void* memp, IData start, IData end) VL_MT_SAFE {
    VL_WRITEMEM_Q(hex, width, depth, array_lsb, fnwords, filename, memp, start, end); }

extern void VL_WRITEF(const char* formatp, ...);
extern void VL_FWRITEF(IData fpi, const char* formatp, ...);

extern IData VL_FSCANF_IX(IData fpi, const char* formatp, ...);
extern IData VL_SSCANF_IIX(int lbits, IData ld, const char* formatp, ...);
extern IData VL_SSCANF_IQX(int lbits, QData ld, const char* formatp, ...);
extern IData VL_SSCANF_IWX(int lbits, WDataInP lwp, const char* formatp, ...);

extern void VL_SFORMAT_X(int obits, CData& destr, const char* formatp, ...);
extern void VL_SFORMAT_X(int obits, SData& destr, const char* formatp, ...);
extern void VL_SFORMAT_X(int obits, IData& destr, const char* formatp, ...);
extern void VL_SFORMAT_X(int obits, QData& destr, const char* formatp, ...);
extern void VL_SFORMAT_X(int obits, void* destp, const char* formatp, ...);

extern IData VL_SYSTEM_IW(int lhswords, WDataInP lhsp);
extern IData VL_SYSTEM_IQ(QData lhs);
inline IData VL_SYSTEM_II(IData lhs) VL_MT_SAFE { return VL_SYSTEM_IQ(lhs); }

extern IData VL_TESTPLUSARGS_I(const char* formatp);
extern const char* vl_mc_scan_plusargs(const char* prefixp);  // PLIish

//=========================================================================
// Base macros

/// Return true if data[bit] set; not 0/1 return, but 0/non-zero return.
#define VL_BITISSET_I(data,bit) ((data) & (VL_UL(1) << VL_BITBIT_I(bit)))
#define VL_BITISSET_Q(data,bit) ((data) & (VL_ULL(1) << VL_BITBIT_Q(bit)))
#define VL_BITISSET_W(data,bit) ((data)[VL_BITWORD_I(bit)] & (VL_UL(1) << VL_BITBIT_I(bit)))
#define VL_BITISSETLIMIT_W(data,width,bit) \
    (((bit)<(width)) && (data)[VL_BITWORD_I(bit)] & (VL_UL(1) << VL_BITBIT_I(bit)))

/// Shift appropriate word by bit. Does not account for wrapping between two words
#define VL_BITRSHIFT_W(data,bit) ((data)[VL_BITWORD_I(bit)] >> VL_BITBIT_I(bit))

/// Create two 32-bit words from quadword
/// WData is always at least 2 words; does not clean upper bits
#define VL_SET_WQ(owp,data) { (owp)[0] = static_cast<IData>(data);  \
        (owp)[1] = static_cast<IData>((data)>>VL_WORDSIZE); }
#define VL_SET_WI(owp,data) { (owp)[0] = static_cast<IData>(data); (owp)[1] = 0; }
#define VL_SET_QW(lwp) \
    ( (static_cast<QData>((lwp)[0]))                                    \
      | (static_cast<QData>((lwp)[1]) << (static_cast<QData>(VL_WORDSIZE)) ))
#define _VL_SET_QII(ld,rd) ((static_cast<QData>(ld)<<VL_ULL(32)) | static_cast<QData>(rd))

/// Return FILE* from IData
extern FILE*  VL_CVT_I_FP(IData lhs);

// Use a union to avoid cast-to-different-size warnings
/// Return void* from QData
static inline void*  VL_CVT_Q_VP(QData lhs) VL_PURE {
    union { void* fp; QData q; } u; u.q=lhs; return u.fp; }
/// Return QData from void*
static inline QData  VL_CVT_VP_Q(void* fp) VL_PURE {
    union { void* fp; QData q; } u; u.q=0; u.fp=fp; return u.q; }
/// Return double from QData (bits, not numerically)
static inline double VL_CVT_D_Q(QData lhs) VL_PURE {
    union { double d; QData q; } u; u.q=lhs; return u.d; }
/// Return QData from double (bits, not numerically)
static inline QData  VL_CVT_Q_D(double lhs) VL_PURE {
    union { double d; QData q; } u; u.d=lhs; return u.q; }
/// Return double from QData (numeric)
static inline double VL_ITOR_D_I(IData lhs) VL_PURE {
    return static_cast<double>(static_cast<vlsint32_t>(lhs)); }
/// Return QData from double (numeric)
static inline IData  VL_RTOI_I_D(double lhs) VL_PURE {
    return static_cast<vlsint32_t>(VL_TRUNC(lhs)); }
/// Return QData from double (numeric)
static inline IData  VL_RTOIROUND_I_D(double lhs) VL_PURE {
    return static_cast<vlsint32_t>(VL_ROUND(lhs)); }

// Sign extend such that if MSB set, we get ffff_ffff, else 0s
// (Requires clean input)
#define VL_SIGN_I(nbits,lhs)      ((lhs) >> VL_BITBIT_I((nbits) - VL_UL(1)))
#define VL_SIGN_Q(nbits,lhs)      ((lhs) >> VL_BITBIT_Q((nbits) - VL_ULL(1)))
#define VL_SIGN_W(nbits,rwp)      ((rwp)[VL_BITWORD_I((nbits)-VL_UL(1))] >> VL_BITBIT_I((nbits)-VL_UL(1)))
#define VL_SIGNONES_I(nbits,lhs)  (-(VL_SIGN_I(nbits, lhs)))

// Sign bit extended up to MSB, doesn't include unsigned portion
// Optimization bug in GCC 3.3 returns different bitmasks to later states for
static inline IData VL_EXTENDSIGN_I(int lbits, IData lhs) VL_PURE {
    return (-((lhs)&(VL_UL(1)<<(lbits-1)))); }
static inline QData VL_EXTENDSIGN_Q(int lbits, QData lhs) VL_PURE {
    return (-((lhs)&(VL_ULL(1)<<(lbits-1)))); }

// Debugging prints
extern void _VL_DEBUG_PRINT_W(int lbits, WDataInP iwp);

//=========================================================================
// Pli macros

#ifndef VL_TIME_PRECISION
# define VL_TIME_PRECISION (-12)  ///< Timescale units only for for VPI return - picoseconds
#endif
#ifndef VL_TIME_MULTIPLIER
# define VL_TIME_MULTIPLIER 1
#endif

/// Return current simulation time
#if defined(SYSTEMC_VERSION) && (SYSTEMC_VERSION>20011000)
# define VL_TIME_I() (static_cast<IData>(sc_time_stamp().to_default_time_units()*VL_TIME_MULTIPLIER))
# define VL_TIME_Q() (static_cast<QData>(sc_time_stamp().to_default_time_units()*VL_TIME_MULTIPLIER))
# define VL_TIME_D() (static_cast<double>(sc_time_stamp().to_default_time_units()*VL_TIME_MULTIPLIER))
#else
# define VL_TIME_I() (static_cast<IData>(sc_time_stamp()*VL_TIME_MULTIPLIER))
# define VL_TIME_Q() (static_cast<QData>(sc_time_stamp()*VL_TIME_MULTIPLIER))
# define VL_TIME_D() (static_cast<double>(sc_time_stamp()*VL_TIME_MULTIPLIER))
extern double sc_time_stamp();
#endif

/// Evaluate expression if debug enabled
#ifdef VL_DEBUG
# define VL_DEBUG_IF(text) {if (VL_UNLIKELY(Verilated::debug())) {text}}
#else
# define VL_DEBUG_IF(text)
#endif

/// Collect coverage analysis for this line
#ifndef SP_AUTO_COVER3
# define SP_AUTO_COVER3(what,file,line)
#endif


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

// Output clean
// EMIT_RULE: VL_CLEAN:  oclean=clean; obits=lbits;
#define VL_CLEAN_II(obits,lbits,lhs) ((lhs) & VL_MASK_I(obits))
#define VL_CLEAN_QQ(obits,lbits,lhs) ((lhs) & VL_MASK_Q(obits))

// EMIT_RULE: VL_ASSIGNCLEAN:  oclean=clean; obits==lbits;
#define VL_ASSIGNCLEAN_W(obits,owp,lwp) VL_CLEAN_WW((obits), (obits), (owp), (lwp))
static inline WDataOutP _VL_CLEAN_INPLACE_W(int obits, WDataOutP owp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    owp[words-1] &= VL_MASK_I(obits);
    return owp;
}
static inline WDataOutP VL_CLEAN_WW(int obits, int, WDataOutP owp, WDataInP lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i=0; (i < (words-1)); ++i) owp[i] = lwp[i];
    owp[words-1] = lwp[words-1] & VL_MASK_I(obits);
    return owp;
}
static inline WDataOutP VL_ZERO_W(int obits, WDataOutP owp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i=0; i < words; ++i) owp[i] = 0;
    return owp;
}
static inline WDataOutP VL_ALLONES_W(int obits, WDataOutP owp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i=0; (i < (words-1)); ++i) owp[i] = ~VL_UL(0);
    owp[words-1] = VL_MASK_I(obits);
    return owp;
}

// EMIT_RULE: VL_ASSIGN:  oclean=rclean; obits==lbits;
// For now, we always have a clean rhs.
// Note: If a ASSIGN isn't clean, use VL_ASSIGNCLEAN instead to do the same thing.
static inline WDataOutP VL_ASSIGN_W(int obits, WDataOutP owp, WDataInP lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i=0; i < words; ++i) owp[i] = lwp[i];
    return owp;
}

// EMIT_RULE: VL_ASSIGNBIT:  rclean=clean;
static inline void VL_ASSIGNBIT_II(int, int bit, CData& lhsr, IData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_UL(1)<<VL_BITBIT_I(bit)))
            | (rhs<<VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_II(int, int bit, SData& lhsr, IData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_UL(1)<<VL_BITBIT_I(bit)))
            | (rhs<<VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_II(int, int bit, IData& lhsr, IData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_UL(1)<<VL_BITBIT_I(bit)))
            | (rhs<<VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_QI(int, int bit, QData& lhsr, QData rhs) VL_PURE {
    lhsr = ((lhsr & ~(VL_ULL(1)<<VL_BITBIT_Q(bit)))
            | (rhs<<VL_BITBIT_Q(bit)));
}
static inline void VL_ASSIGNBIT_WI(int, int bit, WDataOutP owp, IData rhs) VL_MT_SAFE {
    IData orig = owp[VL_BITWORD_I(bit)];
    owp[VL_BITWORD_I(bit)] = ((orig & ~(VL_UL(1)<<VL_BITBIT_I(bit)))
                              | (rhs<<VL_BITBIT_I(bit)));
}
// Alternative form that is an instruction faster when rhs is constant one.
static inline void VL_ASSIGNBIT_IO(int, int bit, CData& lhsr, IData) VL_PURE {
    lhsr = (lhsr | (VL_UL(1)<<VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_IO(int, int bit, SData& lhsr, IData) VL_PURE {
    lhsr = (lhsr | (VL_UL(1)<<VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_IO(int, int bit, IData& lhsr, IData) VL_PURE {
    lhsr = (lhsr | (VL_UL(1)<<VL_BITBIT_I(bit)));
}
static inline void VL_ASSIGNBIT_QO(int, int bit, QData& lhsr, IData) VL_PURE {
    lhsr = (lhsr | (VL_ULL(1)<<VL_BITBIT_Q(bit)));
}
static inline void VL_ASSIGNBIT_WO(int, int bit, WDataOutP owp, IData) VL_MT_SAFE {
    IData orig = owp[VL_BITWORD_I(bit)];
    owp[VL_BITWORD_I(bit)] = (orig |  (VL_UL(1)<<VL_BITBIT_I(bit)));
}

//===================================================================
// SYSTEMC OPERATORS
// Copying verilog format to systemc integers and bit vectors.
// Get a SystemC variable

#define VL_ASSIGN_ISI(obits,vvar,svar) { (vvar) = VL_CLEAN_II((obits), (obits), (svar).read()); }
#define VL_ASSIGN_QSQ(obits,vvar,svar) { (vvar) = VL_CLEAN_QQ((obits), (obits), (svar).read()); }

#define VL_ASSIGN_ISW(obits,od,svar) {                          \
        (od) = ((svar).read().get_word(0)) & VL_MASK_I(obits);  \
    }
#define VL_ASSIGN_QSW(obits,od,svar) {                                  \
        (od) = ((static_cast<QData>((svar).read().get_word(1)))<<VL_WORDSIZE \
                | (svar).read().get_word(0))                            \
            & VL_MASK_Q(obits);                                         \
    }
#define VL_ASSIGN_WSW(obits,owp,svar) {                                 \
        int words = VL_WORDS_I(obits);                                  \
        for (int i=0; i < words; ++i) (owp)[i] = (svar).read().get_word(i); \
        (owp)[words-1] &= VL_MASK_I(obits);                             \
    }

#define VL_ASSIGN_ISU(obits,vvar,svar) { (vvar) = VL_CLEAN_II((obits), (obits), (svar).read().to_uint()); }
#define VL_ASSIGN_QSU(obits,vvar,svar) { (vvar) = VL_CLEAN_QQ((obits), (obits), (svar).read().to_uint64()); }
#define VL_ASSIGN_WSB(obits,owp,svar) {                                 \
        int words = VL_WORDS_I(obits);                                  \
        sc_biguint<(obits)> _butemp = (svar).read();                    \
        for (int i=0; i < words; ++i) {                                 \
            int msb = ((i+1)*VL_WORDSIZE) - 1;                          \
            msb = (msb >= (obits)) ? ((obits)-1) : msb;                 \
            (owp)[i] = _butemp.range(msb, i*VL_WORDSIZE).to_uint();     \
        }                                                               \
        (owp)[words-1] &= VL_MASK_I(obits);                             \
    }

// Copying verilog format from systemc integers and bit vectors.
// Set a SystemC variable

#define VL_ASSIGN_SII(obits,svar,vvar) { (svar).write(vvar); }
#define VL_ASSIGN_SQQ(obits,svar,vvar) { (svar).write(vvar); }

#define VL_ASSIGN_SWI(obits,svar,rd) {          \
        sc_bv<(obits)> _bvtemp;                 \
        _bvtemp.set_word(0, (rd));              \
        (svar).write(_bvtemp);                  \
    }
#define VL_ASSIGN_SWQ(obits,svar,rd) {                                  \
        sc_bv<(obits)> _bvtemp;                                         \
        _bvtemp.set_word(0, static_cast<IData>(rd));                    \
        _bvtemp.set_word(1, static_cast<IData>((rd)>>VL_WORDSIZE));     \
        (svar).write(_bvtemp);                                          \
    }
#define VL_ASSIGN_SWW(obits,svar,rwp) {                                 \
        sc_bv<(obits)> _bvtemp;                                         \
        for (int i=0; i < VL_WORDS_I(obits); ++i) _bvtemp.set_word(i, (rwp)[i]); \
        (svar).write(_bvtemp);                                          \
    }

#define VL_ASSIGN_SUI(obits,svar,rd) { (svar).write(rd); }
#define VL_ASSIGN_SUQ(obits,svar,rd) { (svar).write(rd); }
#define VL_ASSIGN_SBI(obits,svar,rd) { (svar).write(rd); }
#define VL_ASSIGN_SBQ(obits,svar,rd) { (svar).write(rd); }
#define VL_ASSIGN_SBW(obits,svar,rwp) {                         \
        sc_biguint<(obits)> _butemp;                            \
        for (int i=0; i < VL_WORDS_I(obits); ++i) {             \
            int msb = ((i+1)*VL_WORDSIZE) - 1;                  \
            msb = (msb >= (obits)) ? ((obits)-1) : msb;         \
            _butemp.range(msb, i*VL_WORDSIZE) = (rwp)[i];       \
        }                                                       \
        (svar).write(_butemp);                                  \
    }

//===================================================================
// Extending sizes

// CAREFUL, we're width changing, so obits!=lbits

// Right must be clean because otherwise size increase would pick up bad bits
// EMIT_RULE: VL_EXTEND:  oclean=clean; rclean==clean;
#define VL_EXTEND_II(obits,lbits,lhs) ((lhs))
#define VL_EXTEND_QI(obits,lbits,lhs) (static_cast<QData>(lhs))
#define VL_EXTEND_QQ(obits,lbits,lhs) ((lhs))

static inline WDataOutP VL_EXTEND_WI(int obits, int, WDataOutP owp, IData ld) VL_MT_SAFE {
    // Note for extracts that obits != lbits
    owp[0] = ld;
    for (int i=1; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    return owp;
}
static inline WDataOutP VL_EXTEND_WQ(int obits, int, WDataOutP owp, QData ld) VL_MT_SAFE {
    VL_SET_WQ(owp, ld);
    for (int i=2; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    return owp;
}
static inline WDataOutP VL_EXTEND_WW(int obits, int lbits, WDataOutP owp, WDataInP lwp) VL_MT_SAFE {
    for (int i=0; i < VL_WORDS_I(lbits); ++i) owp[i] = lwp[i];
    for (int i=VL_WORDS_I(lbits); i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    return owp;
}

// EMIT_RULE: VL_EXTENDS:  oclean=*dirty*; obits=lbits;
// Sign extension; output dirty
static inline IData VL_EXTENDS_II(int, int lbits, IData lhs) VL_PURE {
    return VL_EXTENDSIGN_I(lbits, lhs) | lhs;
}
static inline QData VL_EXTENDS_QI(int, int lbits, QData lhs/*Q_as_need_extended*/) VL_PURE {
    return VL_EXTENDSIGN_Q(lbits, lhs) | lhs;
}
static inline QData VL_EXTENDS_QQ(int, int lbits, QData lhs) VL_PURE {
    return VL_EXTENDSIGN_Q(lbits, lhs) | lhs;
}

static inline WDataOutP VL_EXTENDS_WI(int obits, int lbits, WDataOutP owp, IData ld) VL_MT_SAFE {
    IData sign = VL_SIGNONES_I(lbits, ld);
    owp[0] = ld | (sign & ~VL_MASK_I(lbits));
    for (int i=1; i < VL_WORDS_I(obits); ++i) owp[i] = sign;
    return owp;
}
static inline WDataOutP VL_EXTENDS_WQ(int obits, int lbits, WDataOutP owp, QData ld) VL_MT_SAFE {
    VL_SET_WQ(owp, ld);
    IData sign = VL_SIGNONES_I(lbits, owp[1]);
    owp[1] |= sign & ~VL_MASK_I(lbits);
    for (int i=2; i < VL_WORDS_I(obits); ++i) owp[i] = sign;
    return owp;
}
static inline WDataOutP VL_EXTENDS_WW(int obits, int lbits, WDataOutP owp, WDataInP lwp) VL_MT_SAFE {
    for (int i=0; i < VL_WORDS_I(lbits)-1; ++i) owp[i] = lwp[i];
    int lmsw = VL_WORDS_I(lbits)-1;
    IData sign = VL_SIGNONES_I(lbits, lwp[lmsw]);
    owp[lmsw] = lwp[lmsw] | (sign & ~VL_MASK_I(lbits));
    for (int i=VL_WORDS_I(lbits); i < VL_WORDS_I(obits); ++i) owp[i] = sign;
    return owp;
}

//===================================================================
// REDUCTION OPERATORS

// EMIT_RULE: VL_REDAND:  oclean=clean; lclean==clean; obits=1;
#define VL_REDAND_II(obits,lbits,lhs) ((lhs) == VL_MASK_I(lbits))
#define VL_REDAND_IQ(obits,lbits,lhs) ((lhs) == VL_MASK_Q(lbits))
static inline IData VL_REDAND_IW(int, int lbits, WDataInP lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(lbits);
    IData combine = lwp[0];
    for (int i=1; i < words-1; ++i) combine &= lwp[i];
    combine &= ~VL_MASK_I(lbits) | lwp[words-1];
    return ((~combine)==0);
}

// EMIT_RULE: VL_REDOR:  oclean=clean; lclean==clean; obits=1;
#define VL_REDOR_I(lhs) ((lhs)!=0)
#define VL_REDOR_Q(lhs) ((lhs)!=0)
static inline IData VL_REDOR_W(int words, WDataInP lwp) VL_MT_SAFE {
    IData equal = 0;
    for (int i=0; i < words; ++i) equal |= lwp[i];
    return (equal != 0);
}

// EMIT_RULE: VL_REDXOR:  oclean=dirty; obits=1;
static inline IData VL_REDXOR_2(IData r) VL_PURE {
    // Experiments show VL_REDXOR_2 is faster than __builtin_parityl
    r=(r^(r>>1));
    return r;
}
static inline IData VL_REDXOR_4(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r=(r^(r>>1)); r=(r^(r>>2));
    return r;
#endif
}
static inline IData VL_REDXOR_8(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r=(r^(r>>1)); r=(r^(r>>2)); r=(r^(r>>4));
    return r;
#endif
}
static inline IData VL_REDXOR_16(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r=(r^(r>>1)); r=(r^(r>>2)); r=(r^(r>>4)); r=(r^(r>>8));
    return r;
#endif
}
static inline IData VL_REDXOR_32(IData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityl(r);
#else
    r=(r^(r>>1)); r=(r^(r>>2)); r=(r^(r>>4)); r=(r^(r>>8)); r=(r^(r>>16));
    return r;
#endif
}
static inline IData VL_REDXOR_64(QData r) VL_PURE {
#if defined(__GNUC__) && (__GNUC__ >= 4) && !defined(VL_NO_BUILTINS)
    return __builtin_parityll(r);
#else
    r=(r^(r>>1)); r=(r^(r>>2)); r=(r^(r>>4)); r=(r^(r>>8)); r=(r^(r>>16)); r=(r^(r>>32));
    return static_cast<IData>(r);
#endif
}
static inline IData VL_REDXOR_W(int words, WDataInP lwp) VL_MT_SAFE {
    IData r = lwp[0];
    for (int i=1; i < words; ++i) r ^= lwp[i];
    return VL_REDXOR_32(r);
}

// EMIT_RULE: VL_COUNTONES_II:  oclean = false; lhs clean
static inline IData VL_COUNTONES_I(IData lhs) VL_PURE {
    // This is faster than __builtin_popcountl
    IData r = lhs - ((lhs >> 1) & 033333333333) - ((lhs >> 2) & 011111111111);
    r = (r + (r>>3)) & 030707070707;
    r = (r + (r>>6));
    r = (r + (r>>12) + (r>>24)) & 077;
    return r;
}
static inline IData VL_COUNTONES_Q(QData lhs) VL_PURE {
    return VL_COUNTONES_I(static_cast<IData>(lhs)) + VL_COUNTONES_I(static_cast<IData>(lhs>>32));
}
static inline IData VL_COUNTONES_W(int words, WDataInP lwp) VL_MT_SAFE {
    IData r = 0;
    for (int i=0; (i < words); ++i) r+=VL_COUNTONES_I(lwp[i]);
    return r;
}

static inline IData VL_ONEHOT_I(IData lhs) VL_PURE {
    return (((lhs & (lhs-1))==0) & (lhs!=0));
}
static inline IData VL_ONEHOT_Q(QData lhs) VL_PURE {
    return (((lhs & (lhs-1))==0) & (lhs!=0));
}
static inline IData VL_ONEHOT_W(int words, WDataInP lwp) VL_MT_SAFE {
    IData one = 0;
    for (int i=0; (i < words); ++i) {
        if (lwp[i]) {
            if (one) return 0;
            one = 1;
            if (lwp[i] & (lwp[i]-1)) return 0;
        }
    }
    return one;
}

static inline IData VL_ONEHOT0_I(IData lhs) VL_PURE {
    return ((lhs & (lhs-1))==0);
}
static inline IData VL_ONEHOT0_Q(QData lhs) VL_PURE {
    return ((lhs & (lhs-1))==0);
}
static inline IData VL_ONEHOT0_W(int words, WDataInP lwp) VL_MT_SAFE {
    bool one = false;
    for (int i=0; (i < words); ++i) {
        if (lwp[i]) {
            if (one) return 0;
            one = true;
            if (lwp[i] & (lwp[i]-1)) return 0;
        }
    }
    return 1;
}

static inline IData VL_CLOG2_I(IData lhs) VL_PURE {
    // There are faster algorithms, or fls GCC4 builtins, but rarely used
    if (VL_UNLIKELY(!lhs)) return 0;
    lhs--;
    int shifts = 0;
    for (; lhs!=0; ++shifts) lhs = lhs >> 1;
    return shifts;
}
static inline IData VL_CLOG2_Q(QData lhs) VL_PURE {
    if (VL_UNLIKELY(!lhs)) return 0;
    lhs--;
    int shifts = 0;
    for (; lhs!=0; ++shifts) lhs = lhs >> VL_ULL(1);
    return shifts;
}
static inline IData VL_CLOG2_W(int words, WDataInP lwp) VL_MT_SAFE {
    IData adjust = (VL_COUNTONES_W(words, lwp)==1) ? 0 : 1;
    for (int i=words-1; i>=0; --i) {
        if (VL_UNLIKELY(lwp[i])) {  // Shorter worst case if predict not taken
            for (int bit=31; bit>=0; --bit) {
                if (VL_UNLIKELY(VL_BITISSET_I(lwp[i], bit))) {
                    return i*VL_WORDSIZE + bit + adjust;
                }
            }
            // Can't get here - one bit must be set
        }
    }
    return 0;
}

static inline IData VL_MOSTSETBITP1_W(int words, WDataInP lwp) VL_MT_SAFE {
    // MSB set bit plus one; similar to FLS.  0=value is zero
    for (int i=words-1; i>=0; --i) {
        if (VL_UNLIKELY(lwp[i])) {  // Shorter worst case if predict not taken
            for (int bit=31; bit>=0; --bit) {
                if (VL_UNLIKELY(VL_BITISSET_I(lwp[i], bit))) {
                    return i*VL_WORDSIZE + bit + 1;
                }
            }
            // Can't get here - one bit must be set
        }
    }
    return 0;
}

//===================================================================
// SIMPLE LOGICAL OPERATORS

// EMIT_RULE: VL_AND:  oclean=lclean||rclean; obits=lbits; lbits==rbits;
static inline WDataOutP VL_AND_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; (i < words); ++i) owp[i] = (lwp[i] & rwp[i]);
    return owp;
}
// EMIT_RULE: VL_OR:   oclean=lclean&&rclean; obits=lbits; lbits==rbits;
static inline WDataOutP VL_OR_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; (i < words); ++i) owp[i] = (lwp[i] | rwp[i]);
    return owp;
}
// EMIT_RULE: VL_CHANGEXOR:  oclean=1; obits=32; lbits==rbits;
static inline IData VL_CHANGEXOR_W(int words, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    IData od = 0;
    for (int i=0; (i < words); ++i) od |= (lwp[i] ^ rwp[i]);
    return(od);
}
// EMIT_RULE: VL_XOR:  oclean=lclean&&rclean; obits=lbits; lbits==rbits;
static inline WDataOutP VL_XOR_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; (i < words); ++i) owp[i] = (lwp[i] ^ rwp[i]);
    return owp;
}
// EMIT_RULE: VL_XNOR:  oclean=dirty; obits=lbits; lbits==rbits;
static inline WDataOutP VL_XNOR_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; (i < words); ++i) owp[i] = (lwp[i] ^ ~rwp[i]);
    return owp;
}
// EMIT_RULE: VL_NOT:  oclean=dirty; obits=lbits;
static inline WDataOutP VL_NOT_W(int words, WDataOutP owp, WDataInP lwp) VL_MT_SAFE {
    for (int i=0; i < words; ++i) owp[i] = ~(lwp[i]);
    return owp;
}

//=========================================================================
// Logical comparisons

// EMIT_RULE: VL_EQ:  oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_NEQ: oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_LT:  oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_GT:  oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_GTE: oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
// EMIT_RULE: VL_LTE: oclean=clean; lclean==clean; rclean==clean; obits=1; lbits==rbits;
#define VL_NEQ_W(words,lwp,rwp)         (!VL_EQ_W(words,lwp,rwp))
#define VL_LT_W(words,lwp,rwp)          (_VL_CMP_W(words,lwp,rwp)<0)
#define VL_LTE_W(words,lwp,rwp)         (_VL_CMP_W(words,lwp,rwp)<=0)
#define VL_GT_W(words,lwp,rwp)          (_VL_CMP_W(words,lwp,rwp)>0)
#define VL_GTE_W(words,lwp,rwp)         (_VL_CMP_W(words,lwp,rwp)>=0)

// Output clean, <lhs> AND <rhs> MUST BE CLEAN
static inline IData VL_EQ_W(int words, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    int nequal = 0;
    for (int i=0; (i < words); ++i) nequal |= (lwp[i] ^ rwp[i]);
    return (nequal==0);
}

// Internal usage
static inline int _VL_CMP_W(int words, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=words-1; i>=0; --i) {
        if (lwp[i] > rwp[i]) return 1;
        if (lwp[i] < rwp[i]) return -1;
    }
    return(0);  // ==
}

#define VL_LTS_IWW(obits,lbits,rbbits,lwp,rwp)          (_VL_CMPS_W(lbits,lwp,rwp)<0)
#define VL_LTES_IWW(obits,lbits,rbits,lwp,rwp)          (_VL_CMPS_W(lbits,lwp,rwp)<=0)
#define VL_GTS_IWW(obits,lbits,rbits,lwp,rwp)           (_VL_CMPS_W(lbits,lwp,rwp)>0)
#define VL_GTES_IWW(obits,lbits,rbits,lwp,rwp)          (_VL_CMPS_W(lbits,lwp,rwp)>=0)

static inline IData VL_GTS_III(int, int lbits, int, IData lhs, IData rhs) VL_PURE {
    // For lbits==32, this becomes just a single instruction, otherwise ~5.
    // GCC 3.3.4 sign extension bugs on AMD64 architecture force us to use quad logic
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);  // Q for gcc
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);  // Q for gcc
    return lhs_signed > rhs_signed;
}
static inline IData VL_GTS_IQQ(int, int lbits, int, QData lhs, QData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed > rhs_signed;
}

static inline IData VL_GTES_III(int, int lbits, int, IData lhs, IData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);  // Q for gcc
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);  // Q for gcc
    return lhs_signed >= rhs_signed;
}
static inline IData VL_GTES_IQQ(int, int lbits, int, QData lhs, QData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed >= rhs_signed;
}

static inline IData VL_LTS_III(int, int lbits, int, IData lhs, IData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);  // Q for gcc
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);  // Q for gcc
    return lhs_signed < rhs_signed;
}
static inline IData VL_LTS_IQQ(int, int lbits, int, QData lhs, QData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed < rhs_signed;
}

static inline IData VL_LTES_III(int, int lbits, int, IData lhs, IData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);  // Q for gcc
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);  // Q for gcc
    return lhs_signed <= rhs_signed;
}
static inline IData VL_LTES_IQQ(int, int lbits, int, QData lhs, QData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed <= rhs_signed;
}

static inline int _VL_CMPS_W(int lbits, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    int words = VL_WORDS_I(lbits);
    int i = words-1;
    // We need to flip sense if negative comparison
    IData lsign = VL_SIGN_I(lbits, lwp[i]);
    IData rsign = VL_SIGN_I(lbits, rwp[i]);
    if (!lsign && rsign) return  1;  // + > -
    if (lsign && !rsign) return -1;  // - < +
    for (; i>=0; --i) {
        if (lwp[i] > rwp[i]) return 1;
        if (lwp[i] < rwp[i]) return -1;
    }
    return(0);  // ==
}

//=========================================================================
// Math

// EMIT_RULE: VL_MUL:    oclean=dirty; lclean==clean; rclean==clean;
// EMIT_RULE: VL_DIV:    oclean=dirty; lclean==clean; rclean==clean;
// EMIT_RULE: VL_MODDIV: oclean=dirty; lclean==clean; rclean==clean;
#define VL_DIV_III(lbits,lhs,rhs)       (((rhs)==0)?0:(lhs)/(rhs))
#define VL_DIV_QQQ(lbits,lhs,rhs)       (((rhs)==0)?0:(lhs)/(rhs))
#define VL_DIV_WWW(lbits,owp,lwp,rwp)   (_vl_moddiv_w(lbits,owp,lwp,rwp,0))
#define VL_MODDIV_III(lbits,lhs,rhs)    (((rhs)==0)?0:(lhs)%(rhs))
#define VL_MODDIV_QQQ(lbits,lhs,rhs)    (((rhs)==0)?0:(lhs)%(rhs))
#define VL_MODDIV_WWW(lbits,owp,lwp,rwp) (_vl_moddiv_w(lbits,owp,lwp,rwp,1))

static inline WDataOutP VL_ADD_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    QData carry = 0;
    for (int i=0; i<words; ++i) {
        carry = carry + static_cast<QData>(lwp[i]) + static_cast<QData>(rwp[i]);
        owp[i] = (carry & VL_ULL(0xffffffff));
        carry = (carry >> VL_ULL(32)) & VL_ULL(0xffffffff);
    }
    return owp;
}

static inline WDataOutP VL_SUB_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    QData carry = 0;
    for (int i=0; i<words; ++i) {
        carry = carry + static_cast<QData>(lwp[i]) + static_cast<QData>(static_cast<IData>(~rwp[i]));
        if (i==0) ++carry;  // Negation of temp2
        owp[i] = (carry & VL_ULL(0xffffffff));
        carry = (carry >> VL_ULL(32)) & VL_ULL(0xffffffff);
    }
    return owp;
}

// Optimization bug in GCC 2.96 and presumably all-pre GCC 3 versions need this workaround,
// we can't just
//# define VL_NEGATE_I(data) (-(data))
static inline IData  VL_NEGATE_I(IData data) VL_PURE { return -data; }
static inline QData  VL_NEGATE_Q(QData data) VL_PURE { return -data; }

static inline WDataOutP VL_NEGATE_W(int words, WDataOutP owp, WDataInP lwp) VL_MT_SAFE {
    QData carry = 0;
    for (int i=0; i<words; ++i) {
        carry = carry + static_cast<QData>(static_cast<IData>(~lwp[i]));
        if (i==0) ++carry;  // Negation of temp2
        owp[i] = (carry & VL_ULL(0xffffffff));
        carry = (carry >> VL_ULL(32)) & VL_ULL(0xffffffff);
    }
    return owp;
}

static inline WDataOutP VL_MUL_W(int words, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; i<words; ++i) owp[i] = 0;
    for (int lword=0; lword<words; ++lword) {
        for (int rword=0; rword<words; ++rword) {
            QData mul = static_cast<QData>(lwp[lword]) * static_cast<QData>(rwp[rword]);
            for (int qword=lword+rword; qword<words; ++qword) {
                mul += static_cast<QData>(owp[qword]);
                owp[qword] = (mul & VL_ULL(0xffffffff));
                mul = (mul >> VL_ULL(32)) & VL_ULL(0xffffffff);
            }
        }
    }
    // Last output word is dirty
    return owp;
}

static inline IData VL_MULS_III(int, int lbits, int, IData lhs, IData rhs) VL_PURE {
    vlsint32_t lhs_signed = VL_EXTENDS_II(32, lbits, lhs);
    vlsint32_t rhs_signed = VL_EXTENDS_II(32, lbits, rhs);
    return lhs_signed * rhs_signed;
}
static inline QData VL_MULS_QQQ(int, int lbits, int, QData lhs, QData rhs) VL_PURE {
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed * rhs_signed;
}

static inline WDataOutP VL_MULS_WWW(int, int lbits, int, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    int words = VL_WORDS_I(lbits);
    // cppcheck-suppress variableScope
    WData lwstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    // cppcheck-suppress variableScope
    WData rwstore[VL_MULS_MAX_WORDS];
    WDataInP lwusp = lwp;
    WDataInP rwusp = rwp;
    IData lneg = VL_SIGN_I(lbits, lwp[words-1]);
    if (lneg) {  // Negate lhs
        lwusp = lwstore;
        VL_NEGATE_W(words, lwstore, lwp);
        lwstore[words-1] &= VL_MASK_I(lbits);  // Clean it
    }
    IData rneg = VL_SIGN_I(lbits, rwp[words-1]);
    if (rneg) {  // Negate rhs
        rwusp = rwstore;
        VL_NEGATE_W(words, rwstore, rwp);
        rwstore[words-1] &= VL_MASK_I(lbits);  // Clean it
    }
    VL_MUL_W(words, owp, lwusp, rwusp);
    owp[words-1] &= VL_MASK_I(lbits);  // Clean.  Note it's ok for the multiply to overflow into the sign bit
    if ((lneg ^ rneg) & 1) {  // Negate output (not using NEGATE, as owp==lwp)
        QData carry = 0;
        for (int i=0; i<words; ++i) {
            carry = carry + static_cast<QData>(static_cast<IData>(~owp[i]));
            if (i==0) ++carry;  // Negation of temp2
            owp[i] = (carry & VL_ULL(0xffffffff));
            carry = (carry >> VL_ULL(32)) & VL_ULL(0xffffffff);
        }
        //Not needed: owp[words-1] |= 1<<VL_BITBIT_I(lbits-1);  // Set sign bit
    }
    // Last output word is dirty
    return owp;
}

static inline IData VL_DIVS_III(int lbits, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs==0)) return 0;
    vlsint32_t lhs_signed = VL_EXTENDS_II(32, lbits, lhs);
    vlsint32_t rhs_signed = VL_EXTENDS_II(32, lbits, rhs);
    return lhs_signed / rhs_signed;
}
static inline QData VL_DIVS_QQQ(int lbits, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs==0)) return 0;
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed / rhs_signed;
}
static inline IData VL_MODDIVS_III(int lbits, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs==0)) return 0;
    vlsint32_t lhs_signed = VL_EXTENDS_II(32, lbits, lhs);
    vlsint32_t rhs_signed = VL_EXTENDS_II(32, lbits, rhs);
    return lhs_signed % rhs_signed;
}
static inline QData VL_MODDIVS_QQQ(int lbits, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs==0)) return 0;
    vlsint64_t lhs_signed = VL_EXTENDS_QQ(64, lbits, lhs);
    vlsint64_t rhs_signed = VL_EXTENDS_QQ(64, lbits, rhs);
    return lhs_signed % rhs_signed;
}

static inline WDataOutP VL_DIVS_WWW(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    int words = VL_WORDS_I(lbits);
    IData lsign = VL_SIGN_I(lbits, lwp[words-1]);
    IData rsign = VL_SIGN_I(lbits, rwp[words-1]);
    // cppcheck-suppress variableScope
    WData lwstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    // cppcheck-suppress variableScope
    WData rwstore[VL_MULS_MAX_WORDS];
    WDataInP ltup = lwp;
    WDataInP rtup = rwp;
    if (lsign) { ltup = _VL_CLEAN_INPLACE_W(lbits, VL_NEGATE_W(VL_WORDS_I(lbits), lwstore, lwp)); }
    if (rsign) { rtup = _VL_CLEAN_INPLACE_W(lbits, VL_NEGATE_W(VL_WORDS_I(lbits), rwstore, rwp)); }
    if ((lsign && !rsign) || (!lsign && rsign)) {
        IData qNoSign[VL_MULS_MAX_WORDS];
        VL_DIV_WWW(lbits, qNoSign, ltup, rtup);
        _VL_CLEAN_INPLACE_W(lbits, VL_NEGATE_W(VL_WORDS_I(lbits), owp, qNoSign));
        return owp;
    } else {
        return VL_DIV_WWW(lbits, owp, ltup, rtup);
    }
}
static inline WDataOutP VL_MODDIVS_WWW(int lbits, WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    int words = VL_WORDS_I(lbits);
    IData lsign = VL_SIGN_I(lbits, lwp[words-1]);
    IData rsign = VL_SIGN_I(lbits, rwp[words-1]);
    // cppcheck-suppress variableScope
    WData lwstore[VL_MULS_MAX_WORDS];  // Fixed size, as MSVC++ doesn't allow [words] here
    // cppcheck-suppress variableScope
    WData rwstore[VL_MULS_MAX_WORDS];
    WDataInP ltup = lwp;
    WDataInP rtup = rwp;
    if (lsign) { ltup = _VL_CLEAN_INPLACE_W(lbits, VL_NEGATE_W(VL_WORDS_I(lbits), lwstore, lwp)); }
    if (rsign) { rtup = _VL_CLEAN_INPLACE_W(lbits, VL_NEGATE_W(VL_WORDS_I(lbits), rwstore, rwp)); }
    if (lsign) {  // Only dividend sign matters for modulus
        WData qNoSign[VL_MULS_MAX_WORDS];
        VL_MODDIV_WWW(lbits, qNoSign, ltup, rtup);
        _VL_CLEAN_INPLACE_W(lbits, VL_NEGATE_W(VL_WORDS_I(lbits), owp, qNoSign));
        return owp;
    } else {
        return VL_MODDIV_WWW(lbits, owp, ltup, rtup);
    }
}

#define VL_POW_IIQ(obits,lbits,rbits,lhs,rhs) VL_POW_QQQ(obits,lbits,rbits,lhs,rhs)
#define VL_POW_IIW(obits,lbits,rbits,lhs,rwp) VL_POW_QQW(obits,lbits,rbits,lhs,rwp)
#define VL_POW_QQI(obits,lbits,rbits,lhs,rhs) VL_POW_QQQ(obits,lbits,rbits,lhs,rhs)
#define VL_POW_WWI(obits,lbits,rbits,owp,lwp,rhs) VL_POW_WWQ(obits,lbits,rbits,owp,lwp,rhs)

static inline IData VL_POW_III(int, int, int rbits, IData lhs, IData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs==0)) return 1;
    if (VL_UNLIKELY(lhs==0)) return 0;
    IData power = lhs;
    IData out = 1;
    for (int i=0; i<rbits; ++i) {
        if (i>0) power = power*power;
        if (rhs & (VL_ULL(1)<<i)) out *= power;
    }
    return out;
}
static inline QData VL_POW_QQQ(int, int, int rbits, QData lhs, QData rhs) VL_PURE {
    if (VL_UNLIKELY(rhs==0)) return 1;
    if (VL_UNLIKELY(lhs==0)) return 0;
    QData power = lhs;
    QData out = VL_ULL(1);
    for (int i=0; i<rbits; ++i) {
        if (i>0) power = power*power;
        if (rhs & (VL_ULL(1)<<i)) out *= power;
    }
    return out;
}
WDataOutP VL_POW_WWW(int obits, int, int rbits, WDataOutP owp, WDataInP lwp, WDataInP rwp);
WDataOutP VL_POW_WWQ(int obits, int, int rbits, WDataOutP owp, WDataInP lwp, QData rhs);
QData VL_POW_QQW(int obits, int, int rbits, QData lhs, WDataInP rwp);

#define VL_POWSS_IIQ(obits,lbits,rbits,lhs,rhs,lsign,rsign) \
    VL_POWSS_QQQ(obits,lbits,rbits,lhs,rhs,lsign,rsign)
#define VL_POWSS_IIQ(obits,lbits,rbits,lhs,rhs,lsign,rsign) \
    VL_POWSS_QQQ(obits,lbits,rbits,lhs,rhs,lsign,rsign)
#define VL_POWSS_IIW(obits,lbits,rbits,lhs,rwp,lsign,rsign) \
    VL_POWSS_QQW(obits,lbits,rbits,lhs,rwp,lsign,rsign)
#define VL_POWSS_QQI(obits,lbits,rbits,lhs,rhs,lsign,rsign) \
    VL_POWSS_QQQ(obits,lbits,rbits,lhs,rhs,lsign,rsign)
#define VL_POWSS_WWI(obits,lbits,rbits,owp,lwp,rhs,lsign,rsign) \
    VL_POWSS_WWQ(obits,lbits,rbits,owp,lwp,rhs,lsign,rsign)

static inline IData VL_POWSS_III(int obits, int, int rbits,
                                 IData lhs, IData rhs, bool lsign, bool rsign) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs==0)) return 1;
    if (rsign && VL_SIGN_I(rbits, rhs)) {
        if (lhs==0) return 0;  // "X"
        else if (lhs==1) return 1;
        else if (lsign && lhs==VL_MASK_I(obits)) {  // -1
            if (rhs & 1) return VL_MASK_I(obits);  // -1^odd=-1
            else return 1;  // -1^even=1
        }
        return 0;
    }
    return VL_POW_III(obits, rbits, rbits, lhs, rhs);
}
static inline QData VL_POWSS_QQQ(int obits, int, int rbits,
                                 QData lhs, QData rhs, bool lsign, bool rsign) VL_MT_SAFE {
    if (VL_UNLIKELY(rhs==0)) return 1;
    if (rsign && VL_SIGN_I(rbits, rhs)) {
        if (lhs==0) return 0;  // "X"
        else if (lhs==1) return 1;
        else if (lsign && lhs==VL_MASK_I(obits)) {  // -1
            if (rhs & 1) return VL_MASK_I(obits);  // -1^odd=-1
            else return 1;  // -1^even=1
        }
        return 0;
    }
    return VL_POW_QQQ(obits, rbits, rbits, lhs, rhs);
}
WDataOutP VL_POWSS_WWW(int obits, int, int rbits,
                       WDataOutP owp, WDataInP lwp, WDataInP rwp, bool lsign, bool rsign);
WDataOutP VL_POWSS_WWQ(int obits, int, int rbits,
                       WDataOutP owp, WDataInP lwp, QData rhs, bool lsign, bool rsign);
QData VL_POWSS_QQW(int obits, int, int rbits,
                   QData lhs, WDataInP rwp, bool lsign, bool rsign);

//===================================================================
// Concat/replication

// INTERNAL: Stuff LHS bit 0++ into OUTPUT at specified offset
// ld may be "dirty", output is clean
static inline void _VL_INSERT_II(int, CData& lhsr, IData ld, int hbit, int lbit) VL_PURE {
    IData insmask = (VL_MASK_I(hbit-lbit+1))<<lbit;
    lhsr = (lhsr & ~insmask) | ((ld<<lbit) & insmask);
}
static inline void _VL_INSERT_II(int, SData& lhsr, IData ld, int hbit, int lbit) VL_PURE {
    IData insmask = (VL_MASK_I(hbit-lbit+1))<<lbit;
    lhsr = (lhsr & ~insmask) | ((ld<<lbit) & insmask);
}
static inline void _VL_INSERT_II(int, IData& lhsr, IData ld, int hbit, int lbit) VL_PURE {
    IData insmask = (VL_MASK_I(hbit-lbit+1))<<lbit;
    lhsr = (lhsr & ~insmask) | ((ld<<lbit) & insmask);
}
static inline void _VL_INSERT_QQ(int, QData& lhsr, QData ld, int hbit, int lbit) VL_PURE {
    QData insmask = (VL_MASK_Q(hbit-lbit+1))<<lbit;
    lhsr = (lhsr & ~insmask) | ((ld<<lbit) & insmask);
}
static inline void _VL_INSERT_WI(int, WDataOutP owp, IData ld, int hbit, int lbit) VL_MT_SAFE {
    int hoffset = VL_BITBIT_I(hbit);
    int loffset = VL_BITBIT_I(lbit);
    if (hoffset==VL_SIZEBITS_I && loffset==0) {
        // Fast and common case, word based insertion
        owp[VL_BITWORD_I(lbit)] = ld;
    }
    else {
        int hword = VL_BITWORD_I(hbit);
        int lword = VL_BITWORD_I(lbit);
        if (hword==lword) {  // know < 32 bits because above checks it
            IData insmask = (VL_MASK_I(hoffset-loffset+1))<<loffset;
            owp[lword] = (owp[lword] & ~insmask) | ((ld<<loffset) & insmask);
        } else {
            IData hinsmask = (VL_MASK_I(hoffset-0+1))<<0;
            IData linsmask = (VL_MASK_I(31-loffset+1))<<loffset;
            int nbitsonright = 32-loffset;  // bits that end up in lword
            owp[lword] = (owp[lword] & ~linsmask) | ((ld<<loffset) & linsmask);
            owp[hword] = (owp[hword] & ~hinsmask) | ((ld>>nbitsonright) & hinsmask);
        }
    }
}

// INTERNAL: Stuff large LHS bit 0++ into OUTPUT at specified offset
// lwp may be "dirty"
static inline void _VL_INSERT_WW(int, WDataOutP owp, WDataInP lwp, int hbit, int lbit) VL_MT_SAFE {
    int hoffset = hbit & VL_SIZEBITS_I;
    int loffset = lbit & VL_SIZEBITS_I;
    int lword = VL_BITWORD_I(lbit);
    int words = VL_WORDS_I(hbit-lbit+1);
    if (hoffset==VL_SIZEBITS_I && loffset==0) {
        // Fast and common case, word based insertion
        for (int i=0; i<words; ++i) {
            owp[lword+i] = lwp[i];
        }
    }
    else if (loffset==0) {
        // Non-32bit, but nicely aligned, so stuff all but the last word
        for (int i=0; i<(words-1); ++i) {
            owp[lword+i] = lwp[i];
        }
        IData hinsmask = (VL_MASK_I(hoffset-0+1));  // Know it's not a full word as above fast case handled it
        owp[lword+words-1] = (owp[words+lword-1] & ~hinsmask) | (lwp[words-1] & hinsmask);
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
                IData d = lwp[i]<<loffset;
                IData od = (owp[oword] & ~linsmask) | (d & linsmask);
                if (oword==hword) owp[oword] = (owp[oword] & ~hinsmask) | (od & hinsmask);
                else owp[oword] = od;
            }
            {   // Upper word
                int oword = lword+i+1;
                if (oword <= hword) {
                    IData d = lwp[i]>>nbitsonright;
                    IData od = (d & ~linsmask) | (owp[oword] & linsmask);
                    if (oword==hword) owp[oword] = (owp[oword] & ~hinsmask) | (od & hinsmask);
                    else owp[oword] = od;
                }
            }
        }
    }
}

static inline void _VL_INSERT_WQ(int obits, WDataOutP owp, QData ld, int hbit, int lbit) VL_MT_SAFE {
    WData lwp[2]; VL_SET_WQ(lwp, ld);
    _VL_INSERT_WW(obits, owp, lwp, hbit, lbit);
}

// EMIT_RULE: VL_REPLICATE:  oclean=clean>width32, dirty<=width32; lclean=clean; rclean==clean;
// RHS MUST BE CLEAN CONSTANT.
#define VL_REPLICATE_IOI(obits,lbits,rbits, ld, rep) (-(ld))  // Iff lbits==1
#define VL_REPLICATE_QOI(obits,lbits,rbits, ld, rep) (-(static_cast<QData>(ld)))  // Iff lbits==1

static inline IData VL_REPLICATE_III(int, int lbits, int, IData ld, IData rep) VL_PURE {
    IData returndata = ld;
    for (unsigned i=1; i < rep; ++i){
        returndata = returndata << lbits;
        returndata |= ld;
    }
    return (returndata);
}
static inline QData VL_REPLICATE_QII(int, int lbits, int, IData ld, IData rep) VL_PURE {
    QData returndata = ld;
    for (unsigned i=1; i < rep; ++i){
        returndata = returndata << lbits;
        returndata |= static_cast<QData>(ld);
    }
    return (returndata);
}
static inline WDataOutP VL_REPLICATE_WII(int obits, int lbits, int,
                                         WDataOutP owp, IData ld, IData rep) VL_MT_SAFE {
    owp[0] = ld;
    for (unsigned i=1; i < rep; ++i){
        _VL_INSERT_WI(obits, owp, ld, i*lbits+lbits-1, i*lbits);
    }
    return owp;
}
static inline WDataOutP VL_REPLICATE_WQI(int obits, int lbits, int,
                                         WDataOutP owp, QData ld, IData rep) VL_MT_SAFE {
    VL_SET_WQ(owp, ld);
    for (unsigned i=1; i < rep; ++i){
        _VL_INSERT_WQ(obits, owp, ld, i*lbits+lbits-1, i*lbits);
    }
    return owp;
}
static inline WDataOutP VL_REPLICATE_WWI(int obits, int lbits, int,
                                         WDataOutP owp, WDataInP lwp, IData rep) VL_MT_SAFE {
    for (int i=0; i < VL_WORDS_I(lbits); ++i) owp[i] = lwp[i];
    for (unsigned i=1; i < rep; ++i){
        _VL_INSERT_WW(obits, owp, lwp, i*lbits+lbits-1, i*lbits);
    }
    return owp;
}

// Left stream operator. Output will always be clean. LHS and RHS must be clean.
// Special "fast" versions for slice sizes that are a power of 2. These use
// shifts and masks to execute faster than the slower for-loop approach where a
// subset of bits is copied in during each iteration.
static inline IData VL_STREAML_FAST_III(int, int lbits, int, IData ld, IData rd_log2) VL_PURE {
    // Pre-shift bits in most-significant slice:
    //
    // If lbits is not a multiple of the slice size (i.e., lbits % rd != 0),
    // then we end up with a "gap" in our reversed result. For example, if we
    // have a 5-bit Verlilog signal (lbits=5) in an 8-bit C data type:
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
        vluint32_t lbitsFloor = lbits & ~VL_MASK_I(rd_log2);  // max multiple of rd <= lbits
        vluint32_t lbitsRem = lbits - lbitsFloor;  // number of bits in most-sig slice (MSS)
        IData msbMask = VL_MASK_I(lbitsRem) << lbitsFloor;  // mask to sel only bits in MSS
        ret = (ret & ~msbMask) | ((ret & msbMask) << ((VL_UL(1) << rd_log2) - lbitsRem));
    }
    switch (rd_log2) {
        case 0:
            ret = ((ret >> 1) & VL_UL(0x55555555))
                | ((ret & VL_UL(0x55555555)) << 1);  // FALLTHRU
        case 1:
            ret = ((ret >> 2) & VL_UL(0x33333333))
                | ((ret & VL_UL(0x33333333)) << 2);  // FALLTHRU
        case 2:
            ret = ((ret >> 4) & VL_UL(0x0f0f0f0f))
                | ((ret & VL_UL(0x0f0f0f0f)) << 4);  // FALLTHRU
        case 3:
            ret = ((ret >> 8) & VL_UL(0x00ff00ff))
                | ((ret & VL_UL(0x00ff00ff)) << 8);  // FALLTHRU
        case 4:
            ret = ((ret >> 16) | (ret << 16));
    }
    return ret >> (VL_WORDSIZE - lbits);
}

static inline QData VL_STREAML_FAST_QQI(int, int lbits, int, QData ld, IData rd_log2) VL_PURE {
    // Pre-shift bits in most-significant slice (see comment in VL_STREAML_FAST_III)
    QData ret = ld;
    if (rd_log2) {
        vluint32_t lbitsFloor = lbits & ~VL_MASK_I(rd_log2);
        vluint32_t lbitsRem = lbits - lbitsFloor;
        QData msbMask = VL_MASK_Q(lbitsRem) << lbitsFloor;
        ret = (ret & ~msbMask) | ((ret & msbMask) << ((VL_ULL(1) << rd_log2) - lbitsRem));
    }
    switch (rd_log2) {
        case 0:
            ret = (((ret >>  1) & VL_ULL(0x5555555555555555))
                   | ((ret & VL_ULL(0x5555555555555555)) <<  1));  // FALLTHRU
        case 1:
            ret = (((ret >>  2) & VL_ULL(0x3333333333333333))
                   | ((ret & VL_ULL(0x3333333333333333)) <<  2));  // FALLTHRU
        case 2:
            ret = (((ret >>  4) & VL_ULL(0x0f0f0f0f0f0f0f0f))
                   | ((ret & VL_ULL(0x0f0f0f0f0f0f0f0f)) <<  4));  // FALLTHRU
        case 3:
            ret = (((ret >>  8) & VL_ULL(0x00ff00ff00ff00ff))
                   | ((ret & VL_ULL(0x00ff00ff00ff00ff)) <<  8));  // FALLTHRU
        case 4:
            ret = (((ret >> 16) & VL_ULL(0x0000ffff0000ffff))
                   | ((ret & VL_ULL(0x0000ffff0000ffff)) << 16));  // FALLTHRU
        case 5:
            ret = ((ret >> 32) | (ret << 32));
    }
    return ret >> (VL_QUADSIZE - lbits);
}

// Regular "slow" streaming operators
static inline IData VL_STREAML_III(int, int lbits, int, IData ld, IData rd) VL_PURE {
    IData ret = 0;
    // Slice size should never exceed the lhs width
    IData mask = VL_MASK_I(rd);
    for (int istart=0; istart<lbits; istart+=rd) {
        int ostart = lbits-rd-istart;
        ostart = ostart > 0 ? ostart : 0;
        ret |= ((ld >> istart) & mask) << ostart;
    }
    return ret;
}

static inline QData VL_STREAML_QQI(int, int lbits, int, QData ld, IData rd) VL_PURE {
    QData ret = 0;
    // Slice size should never exceed the lhs width
    QData mask = VL_MASK_Q(rd);
    for (int istart=0; istart<lbits; istart+=rd) {
        int ostart = lbits-rd-istart;
        ostart = ostart > 0 ? ostart : 0;
        ret |= ((ld >> istart) & mask) << ostart;
    }
    return ret;
}

static inline WDataOutP VL_STREAML_WWI(int, int lbits, int, WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE {
    VL_ZERO_W(lbits, owp);
    // Slice size should never exceed the lhs width
    int ssize = (rd < static_cast<IData>(lbits)) ? rd : (static_cast<IData>(lbits));
    for (int istart=0; istart<lbits; istart+=rd) {
        int ostart = lbits-rd-istart;
        ostart = ostart > 0 ? ostart : 0;
        for (int sbit=0; sbit<ssize && sbit<lbits-istart; ++sbit) {
            // Extract a single bit from lwp and shift it to the correct
            // location for owp.
            WData bit= (VL_BITRSHIFT_W(lwp, (istart+sbit)) & 1) << VL_BITBIT_I(ostart+sbit);
            owp[VL_BITWORD_I(ostart+sbit)] |= bit;
        }
    }
    return owp;
}

// Because concats are common and wide, it's valuable to always have a clean output.
// Thus we specify inputs must be clean, so we don't need to clean the output.
// Note the bit shifts are always constants, so the adds in these constify out.
// Casts required, as args may be 8 bit entities, and need to shift to appropriate output size
#define VL_CONCAT_III(obits,lbits,rbits,ld,rd) \
    (static_cast<IData>(ld)<<(rbits) | static_cast<IData>(rd))
#define VL_CONCAT_QII(obits,lbits,rbits,ld,rd) \
    (static_cast<QData>(ld)<<(rbits) | static_cast<QData>(rd))
#define VL_CONCAT_QIQ(obits,lbits,rbits,ld,rd) \
    (static_cast<QData>(ld)<<(rbits) | static_cast<QData>(rd))
#define VL_CONCAT_QQI(obits,lbits,rbits,ld,rd) \
    (static_cast<QData>(ld)<<(rbits) | static_cast<QData>(rd))
#define VL_CONCAT_QQQ(obits,lbits,rbits,ld,rd) \
    (static_cast<QData>(ld)<<(rbits) | static_cast<QData>(rd))

static inline WDataOutP VL_CONCAT_WII(int obits, int lbits, int rbits,
                                      WDataOutP owp, IData ld, IData rd) VL_MT_SAFE {
    owp[0] = rd;
    for (int i=1; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WI(obits, owp, ld, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WWI(int obits, int lbits, int rbits,
                                      WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE {
    owp[0] = rd;
    for (int i=1; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WW(obits, owp, lwp, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WIW(int obits, int lbits, int rbits,
                                      WDataOutP owp, IData ld, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; i < VL_WORDS_I(rbits); ++i) owp[i] = rwp[i];
    for (int i=VL_WORDS_I(rbits); i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WI(obits, owp, ld, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WIQ(int obits, int lbits, int rbits,
                                      WDataOutP owp, IData ld, QData rd) VL_MT_SAFE {
    VL_SET_WQ(owp, rd);
    for (int i=2; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WI(obits, owp, ld, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WQI(int obits, int lbits, int rbits,
                                      WDataOutP owp, QData ld, IData rd) VL_MT_SAFE {
    owp[0] = rd;
    for (int i=1; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WQ(obits, owp, ld, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WQQ(int obits, int lbits, int rbits,
                                      WDataOutP owp, QData ld, QData rd) VL_MT_SAFE {
    VL_SET_WQ(owp, rd);
    for (int i=2; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WQ(obits, owp, ld, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WWQ(int obits, int lbits, int rbits,
                                      WDataOutP owp, WDataInP lwp, QData rd) VL_MT_SAFE {
    VL_SET_WQ(owp, rd);
    for (int i=2; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WW(obits, owp, lwp, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WQW(int obits, int lbits, int rbits,
                                      WDataOutP owp, QData ld, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; i < VL_WORDS_I(rbits); ++i) owp[i] = rwp[i];
    for (int i=VL_WORDS_I(rbits); i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WQ(obits, owp, ld, rbits+lbits-1, rbits);
    return owp;
}
static inline WDataOutP VL_CONCAT_WWW(int obits, int lbits, int rbits,
                                      WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=0; i < VL_WORDS_I(rbits); ++i) owp[i] = rwp[i];
    for (int i=VL_WORDS_I(rbits); i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    _VL_INSERT_WW(obits, owp, lwp, rbits+lbits-1, rbits);
    return owp;
}

//===================================================================
// Shifts

// Static shift, used by internal functions
// The output is the same as the input - it overlaps!
static inline void _VL_SHIFTL_INPLACE_W(int obits, WDataOutP iowp, IData rd/*1 or 4*/) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    IData linsmask = VL_MASK_I(rd);
    for (int i=words-1; i>=1; --i) {
        iowp[i] = ((iowp[i]<<rd) & ~linsmask) | ((iowp[i-1] >> (32-rd)) & linsmask);
    }
    iowp[0] = ((iowp[0]<<rd) & ~linsmask);
    iowp[VL_WORDS_I(obits)-1] &= VL_MASK_I(obits);
}

// EMIT_RULE: VL_SHIFTL:  oclean=lclean; rclean==clean;
// Important: Unlike most other funcs, the shift might well be a computed
// expression.  Thus consider this when optimizing.  (And perhaps have 2 funcs?)
static inline WDataOutP VL_SHIFTL_WWI(int obits, int, int, WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE {
    int word_shift = VL_BITWORD_I(rd);
    int bit_shift = VL_BITBIT_I(rd);
    if (rd >= static_cast<IData>(obits)) {  // rd may be huge with MSB set
        for (int i=0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    } else if (bit_shift==0) {  // Aligned word shift (<<0,<<32,<<64 etc)
        for (int i=0; i < word_shift; ++i) owp[i] = 0;
        for (int i=word_shift; i < VL_WORDS_I(obits); ++i) owp[i] = lwp[i-word_shift];
    } else {
        for (int i=0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
        _VL_INSERT_WW(obits, owp, lwp, obits-1, rd);
    }
    return owp;
}
static inline WDataOutP VL_SHIFTL_WWW(int obits, int lbits, int rbits,
                                      WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            return VL_ZERO_W(obits, owp);
        }
    }
    return VL_SHIFTL_WWI(obits, lbits, 32, owp, lwp, rwp[0]);
}
static inline IData VL_SHIFTL_IIW(int obits, int, int rbits, IData lhs, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            return 0;
        }
    }
    return VL_CLEAN_II(obits, obits, lhs<<rwp[0]);
}
static inline QData VL_SHIFTL_QQW(int obits, int, int rbits, QData lhs, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            return 0;
        }
    }
    // Above checks rwp[1]==0 so not needed in below shift
    return VL_CLEAN_QQ(obits, obits, lhs<<(static_cast<QData>(rwp[0])));
}

// EMIT_RULE: VL_SHIFTR:  oclean=lclean; rclean==clean;
// Important: Unlike most other funcs, the shift might well be a computed
// expression.  Thus consider this when optimizing.  (And perhaps have 2 funcs?)
static inline WDataOutP VL_SHIFTR_WWI(int obits, int, int,
                                      WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE {
    int word_shift = VL_BITWORD_I(rd);  // Maybe 0
    int bit_shift = VL_BITBIT_I(rd);
    if (rd >= static_cast<IData>(obits)) {  // rd may be huge with MSB set
        for (int i=0; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    } else if (bit_shift==0) {  // Aligned word shift (>>0,>>32,>>64 etc)
        int copy_words = (VL_WORDS_I(obits)-word_shift);
        for (int i=0; i < copy_words; ++i) owp[i] = lwp[i+word_shift];
        for (int i=copy_words; i < VL_WORDS_I(obits); ++i) owp[i] = 0;
    } else {
        int loffset = rd & VL_SIZEBITS_I;
        int nbitsonright = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int words = VL_WORDS_I(obits-rd);
        for (int i=0; i<words; ++i) {
            owp[i] = lwp[i+word_shift]>>loffset;
            int upperword = i+word_shift+1;
            if (upperword < VL_WORDS_I(obits)) {
                owp[i] |= lwp[upperword]<< nbitsonright;
            }
        }
        for (int i=words; i<VL_WORDS_I(obits); ++i) owp[i]=0;
    }
    return owp;
}
static inline WDataOutP VL_SHIFTR_WWW(int obits, int lbits, int rbits,
                                      WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            return VL_ZERO_W(obits, owp);
        }
    }
    return VL_SHIFTR_WWI(obits, lbits, 32, owp, lwp, rwp[0]);
}
static inline IData VL_SHIFTR_IIW(int obits, int, int rbits, IData lhs, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            return 0;
        }
    }
    return VL_CLEAN_II(obits, obits, lhs>>rwp[0]);
}
static inline QData VL_SHIFTR_QQW(int obits, int, int rbits, QData lhs, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            return 0;
        }
    }
    // Above checks rwp[1]==0 so not needed in below shift
    return VL_CLEAN_QQ(obits, obits, lhs>>(static_cast<QData>(rwp[0])));
}

// EMIT_RULE: VL_SHIFTRS:  oclean=false; lclean=clean, rclean==clean;
static inline IData VL_SHIFTRS_III(int obits, int lbits, int, IData lhs, IData rhs) VL_PURE {
    // Note the C standard does not specify the >> operator as a arithmetic shift!
    // IEEE says signed if output signed, but bit position from lbits;
    // must use lbits for sign; lbits might != obits,
    // an EXTEND(SHIFTRS(...)) can became a SHIFTRS(...) within same 32/64 bit word length
    IData sign    = -(lhs >> (lbits-1));  // ffff_ffff if negative
    IData signext = ~(VL_MASK_I(lbits) >> rhs);  // One with bits where we've shifted "past"
    return (lhs >> rhs) | (sign & VL_CLEAN_II(obits, obits, signext));
}
static inline QData VL_SHIFTRS_QQI(int obits, int lbits, int, QData lhs, IData rhs) VL_PURE {
    QData sign    = -(lhs >> (lbits-1));
    QData signext = ~(VL_MASK_Q(lbits) >> rhs);
    return (lhs >> rhs) | (sign & VL_CLEAN_QQ(obits, obits, signext));
}
static inline IData VL_SHIFTRS_IQI(int obits, int lbits, int rbits,
                                   QData lhs, IData rhs) VL_PURE {
    return static_cast<IData>(VL_SHIFTRS_QQI(obits, lbits, rbits, lhs, rhs));
}
static inline WDataOutP VL_SHIFTRS_WWI(int obits, int lbits, int,
                                       WDataOutP owp, WDataInP lwp, IData rd) VL_MT_SAFE {
    int word_shift = VL_BITWORD_I(rd);
    int bit_shift = VL_BITBIT_I(rd);
    int lmsw = VL_WORDS_I(obits)-1;
    IData sign = VL_SIGNONES_I(lbits, lwp[lmsw]);
    if (rd >= static_cast<IData>(obits)) {  // Shifting past end, sign in all of lbits
        for (int i=0; i <= lmsw; ++i) owp[i] = sign;
        owp[lmsw] &= VL_MASK_I(lbits);
    } else if (bit_shift==0) {  // Aligned word shift (>>0,>>32,>>64 etc)
        int copy_words = (VL_WORDS_I(obits)-word_shift);
        for (int i=0; i < copy_words; ++i) owp[i] = lwp[i+word_shift];
        if (copy_words>=0) owp[copy_words-1] |= ~VL_MASK_I(obits) & sign;
        for (int i=copy_words; i < VL_WORDS_I(obits); ++i) owp[i] = sign;
        owp[lmsw] &= VL_MASK_I(lbits);
    } else {
        int loffset = rd & VL_SIZEBITS_I;
        int nbitsonright = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int words = VL_WORDS_I(obits-rd);
        for (int i=0; i<words; ++i) {
            owp[i] = lwp[i+word_shift]>>loffset;
            int upperword = i+word_shift+1;
            if (upperword < VL_WORDS_I(obits)) {
                owp[i] |= lwp[upperword]<< nbitsonright;
            }
        }
        if (words) owp[words-1] |= sign & ~VL_MASK_I(obits-loffset);
        for (int i=words; i<VL_WORDS_I(obits); ++i) owp[i] = sign;
        owp[lmsw] &= VL_MASK_I(lbits);
    }
    return owp;
}
static inline WDataOutP VL_SHIFTRS_WWW(int obits, int lbits, int rbits,
                                       WDataOutP owp, WDataInP lwp, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            int lmsw = VL_WORDS_I(obits)-1;
            IData sign = VL_SIGNONES_I(lbits, lwp[lmsw]);
            for (int j=0; j <= lmsw; ++j) owp[j] = sign;
            owp[lmsw] &= VL_MASK_I(lbits);
            return owp;
        }
    }
    return VL_SHIFTRS_WWI(obits, lbits, 32, owp, lwp, rwp[0]);
}
static inline IData VL_SHIFTRS_IIW(int obits, int lbits, int rbits,
                                   IData lhs, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            IData sign = -(lhs >> (lbits-1));  // ffff_ffff if negative
            return VL_CLEAN_II(obits, obits, sign);
        }
    }
    return VL_SHIFTRS_III(obits, lbits, 32, lhs, rwp[0]);
}
static inline QData VL_SHIFTRS_QQW(int obits, int lbits, int rbits,
                                   QData lhs, WDataInP rwp) VL_MT_SAFE {
    for (int i=1; i < VL_WORDS_I(rbits); ++i) {
        if (VL_UNLIKELY(rwp[i])) {  // Huge shift 1>>32 or more
            QData sign = -(lhs >> (lbits-1));  // ffff_ffff if negative
            return VL_CLEAN_QQ(obits, obits, sign);
        }
    }
    return VL_SHIFTRS_QQI(obits, lbits, 32, lhs, rwp[0]);
}
static inline IData VL_SHIFTRS_IIQ(int obits, int lbits, int rbits, IData lhs, QData rhs) VL_PURE {
    WData rwp[2]; VL_SET_WQ(rwp, rhs);
    return VL_SHIFTRS_IIW(obits, lbits, rbits, lhs, rwp);
}
static inline QData VL_SHIFTRS_QQQ(int obits, int lbits, int rbits, QData lhs, QData rhs) VL_PURE {
    WData rwp[2]; VL_SET_WQ(rwp, rhs);
    return VL_SHIFTRS_QQW(obits, lbits, rbits, lhs, rwp);
}

//===================================================================
// Bit selection

// EMIT_RULE: VL_BITSEL:  oclean=dirty; rclean==clean;
#define VL_BITSEL_IIII(obits,lbits,rbits,zbits,lhs,rhs) ((lhs)>>(rhs))
#define VL_BITSEL_QIII(obits,lbits,rbits,zbits,lhs,rhs) ((lhs)>>(rhs))
#define VL_BITSEL_QQII(obits,lbits,rbits,zbits,lhs,rhs) ((lhs)>>(rhs))
#define VL_BITSEL_IQII(obits,lbits,rbits,zbits,lhs,rhs) (static_cast<IData>((lhs)>>(rhs)))

static inline IData VL_BITSEL_IWII(int, int lbits, int, int, WDataInP lwp, IData rd) VL_MT_SAFE {
    int word = VL_BITWORD_I(rd);
    if (VL_UNLIKELY(rd > static_cast<IData>(lbits))) {
        return ~0;  // Spec says you can go outside the range of a array.  Don't coredump if so.
        // We return all 1's as that's more likely to find bugs (?) than 0's.
    } else {
        return (lwp[word]>>VL_BITBIT_I(rd));
    }
}

// EMIT_RULE: VL_RANGE:  oclean=lclean;  out=dirty
// <msb> & <lsb> MUST BE CLEAN (currently constant)
#define VL_SEL_IIII(obits,lbits,rbits,tbits,lhs,lsb,width) ((lhs)>>(lsb))
#define VL_SEL_QQII(obits,lbits,rbits,tbits,lhs,lsb,width) ((lhs)>>(lsb))
#define VL_SEL_IQII(obits,lbits,rbits,tbits,lhs,lsb,width) (static_cast<IData>((lhs)>>(lsb)))

static inline IData VL_SEL_IWII(int, int lbits, int, int,
                                WDataInP lwp, IData lsb, IData width) VL_MT_SAFE {
    int msb = lsb+width-1;
    if (VL_UNLIKELY(msb>lbits)) {
        return ~0;  // Spec says you can go outside the range of a array.  Don't coredump if so.
    } else if (VL_BITWORD_I(msb)==VL_BITWORD_I(static_cast<int>(lsb))) {
        return VL_BITRSHIFT_W(lwp, lsb);
    } else {
        // 32 bit extraction may span two words
        int nbitsfromlow = 32-VL_BITBIT_I(lsb);  // bits that come from low word
        return ((lwp[VL_BITWORD_I(msb)]<<nbitsfromlow)
                | VL_BITRSHIFT_W(lwp, lsb));
    }
}

static inline QData VL_SEL_QWII(int, int lbits, int, int,
                                WDataInP lwp, IData lsb, IData width) VL_MT_SAFE {
    int msb = lsb+width-1;
    if (VL_UNLIKELY(msb>lbits)) {
        return ~0;  // Spec says you can go outside the range of a array.  Don't coredump if so.
    } else if (VL_BITWORD_I(msb)==VL_BITWORD_I(static_cast<int>(lsb))) {
        return VL_BITRSHIFT_W(lwp, lsb);
    } else if (VL_BITWORD_I(msb)==1+VL_BITWORD_I(static_cast<int>(lsb))) {
        int nbitsfromlow = 32-VL_BITBIT_I(lsb);
        QData hi = (lwp[VL_BITWORD_I(msb)]);
        QData lo = VL_BITRSHIFT_W(lwp, lsb);
        return (hi<<nbitsfromlow) | lo;
    } else {
        // 64 bit extraction may span three words
        int nbitsfromlow = 32-VL_BITBIT_I(lsb);
        QData hi = (lwp[VL_BITWORD_I(msb)]);
        QData mid= (lwp[VL_BITWORD_I(lsb)+1]);
        QData lo = VL_BITRSHIFT_W(lwp, lsb);
        return (hi<<(nbitsfromlow+32)) | (mid<<nbitsfromlow) | lo;
    }
}

static inline WDataOutP VL_SEL_WWII(int obits, int lbits, int, int,
                                    WDataOutP owp, WDataInP lwp, IData lsb, IData width) VL_MT_SAFE {
    int msb = lsb+width-1;
    int word_shift = VL_BITWORD_I(lsb);
    if (VL_UNLIKELY(msb>lbits)) {  // Outside bounds,
        for (int i=0; i<VL_WORDS_I(obits)-1; ++i) owp[i] = ~0;
        owp[VL_WORDS_I(obits)-1] = VL_MASK_I(obits);
    } else if (VL_BITBIT_I(lsb)==0) {
        // Just a word extract
        for (int i=0; i<VL_WORDS_I(obits); ++i) owp[i] = lwp[i+word_shift];
    } else {
        // Not a _VL_INSERT because the bits come from any bit number and goto bit 0
        int loffset = lsb & VL_SIZEBITS_I;
        int nbitsfromlow = 32-loffset;  // bits that end up in lword (know loffset!=0)
        // Middle words
        int words = VL_WORDS_I(msb-lsb+1);
        for (int i=0; i<words; ++i) {
            owp[i] = lwp[i+word_shift]>>loffset;
            int upperword = i+word_shift+1;
            if (upperword <= static_cast<int>(VL_BITWORD_I(msb))) {
                owp[i] |= lwp[upperword]<< nbitsfromlow;
            }
        }
        for (int i=words; i<VL_WORDS_I(obits); ++i) owp[i]=0;
    }
    return owp;
}

//======================================================================
// Range assignments

// EMIT_RULE: VL_ASSIGNRANGE:  rclean=dirty;
static inline void VL_ASSIGNSEL_IIII(int obits, int lsb, CData& lhsr, IData rhs) VL_PURE {
    _VL_INSERT_II(obits, lhsr, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_IIII(int obits, int lsb, SData& lhsr, IData rhs) VL_PURE {
    _VL_INSERT_II(obits, lhsr, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_IIII(int obits, int lsb, IData& lhsr, IData rhs) VL_PURE {
    _VL_INSERT_II(obits, lhsr, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_QIII(int obits, int lsb, QData& lhsr, IData rhs) VL_PURE {
    _VL_INSERT_QQ(obits, lhsr, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_QQII(int obits, int lsb, QData& lhsr, QData rhs) VL_PURE {
    _VL_INSERT_QQ(obits, lhsr, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_QIIQ(int obits, int lsb, QData& lhsr, QData rhs) VL_PURE {
    _VL_INSERT_QQ(obits, lhsr, rhs, lsb+obits-1, lsb);
}
//static inline void VL_ASSIGNSEL_IIIW(int obits, int lsb, IData& lhsr, WDataInP rwp) VL_MT_SAFE {
// Illegal, as lhs width >= rhs width
static inline void VL_ASSIGNSEL_WIII(int obits, int lsb, WDataOutP owp, IData rhs) VL_MT_SAFE {
    _VL_INSERT_WI(obits, owp, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_WIIQ(int obits, int lsb, WDataOutP owp, QData rhs) VL_MT_SAFE {
    _VL_INSERT_WQ(obits, owp, rhs, lsb+obits-1, lsb);
}
static inline void VL_ASSIGNSEL_WIIW(int obits, int lsb, WDataOutP owp, WDataInP rwp) VL_MT_SAFE {
    _VL_INSERT_WW(obits, owp, rwp, lsb+obits-1, lsb);
}

//======================================================================
// Triops

static inline WDataOutP VL_COND_WIWW(int obits, int, int, int,
                                     WDataOutP owp, int cond,
                                     WDataInP w1p, WDataInP w2p) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i=0; i < words; ++i) owp[i] = cond ? w1p[i] : w2p[i];
    return owp;
}

//======================================================================
// Constification

// VL_CONST_W_#X(int obits, WDataOutP owp, IData data0, .... IData data(#-1))
// Sets wide vector words to specified constant words.
// These macros are used when o might represent more words then are given as constants,
// hence all upper words must be zeroed.
// If changing the number of functions here, also change EMITCINLINES_NUM_CONSTW

#define _END(obits,wordsSet) \
    for(int i=(wordsSet);i<VL_WORDS_I(obits);++i) o[i] = 0; \
    return o

static inline WDataOutP VL_CONST_W_1X(int obits, WDataOutP o,
                                      IData d0) VL_MT_SAFE {
    o[0]=d0;
    _END(obits,1);  }
static inline WDataOutP VL_CONST_W_2X(int obits, WDataOutP o,
                                      IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;
    _END(obits,2);  }
static inline WDataOutP VL_CONST_W_3X(int obits, WDataOutP o,
                                      IData d2, IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;  o[2]=d2;
    _END(obits,3);  }
static inline WDataOutP VL_CONST_W_4X(int obits, WDataOutP o,
                                      IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;
    _END(obits,4);  }
static inline WDataOutP VL_CONST_W_5X(int obits, WDataOutP o,
                                      IData d4,
                                      IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;
    _END(obits,5);  }
static inline WDataOutP VL_CONST_W_6X(int obits, WDataOutP o,
                                      IData d5, IData d4,
                                      IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;  o[5]=d5;
    _END(obits,6);  }
static inline WDataOutP VL_CONST_W_7X(int obits, WDataOutP o,
                                      IData d6, IData d5, IData d4,
                                      IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;  o[5]=d5;  o[6]=d6;
    _END(obits,7);  }
static inline WDataOutP VL_CONST_W_8X(int obits, WDataOutP o,
                                      IData d7, IData d6, IData d5, IData d4,
                                      IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;  o[5]=d5;  o[6]=d6;  o[7]=d7;
    _END(obits,8);  }
//
static inline WDataOutP VL_CONSTHI_W_1X(int obits, int lsb, WDataOutP obase,
                                        IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;
    _END(obits,1);  }
static inline WDataOutP VL_CONSTHI_W_2X(int obits, int lsb, WDataOutP obase,
                                        IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;
    _END(obits,2);  }
static inline WDataOutP VL_CONSTHI_W_3X(int obits, int lsb, WDataOutP obase,
                                        IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;  o[2]=d2;
    _END(obits,3);  }
static inline WDataOutP VL_CONSTHI_W_4X(int obits, int lsb, WDataOutP obase,
                                        IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;
    _END(obits,4);  }
static inline WDataOutP VL_CONSTHI_W_5X(int obits, int lsb, WDataOutP obase,
                                        IData d4,
                                        IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;
    _END(obits,5);  }
static inline WDataOutP VL_CONSTHI_W_6X(int obits, int lsb, WDataOutP obase,
                                        IData d5, IData d4,
                                        IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;  o[5]=d5;
    _END(obits,6);  }
static inline WDataOutP VL_CONSTHI_W_7X(int obits, int lsb, WDataOutP obase,
                                        IData d6, IData d5, IData d4,
                                        IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;  o[5]=d5;  o[6]=d6;
    _END(obits,7);  }
static inline WDataOutP VL_CONSTHI_W_8X(int obits, int lsb, WDataOutP obase,
                                        IData d7, IData d6, IData d5, IData d4,
                                        IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0;  o[1]=d1;  o[2]=d2;  o[3]=d3;  o[4]=d4;  o[5]=d5;  o[6]=d6;  o[7]=d7;
    _END(obits,8);  }

#undef _END

// Partial constant, lower words of vector wider than 8*32, starting at bit number lsb
static inline void VL_CONSTLO_W_8X(int lsb, WDataOutP obase,
                                   IData d7, IData d6, IData d5, IData d4,
                                   IData d3, IData d2, IData d1, IData d0) VL_MT_SAFE {
    WDataOutP o = obase + VL_WORDS_I(lsb);
    o[0]=d0; o[1]=d1; o[2]=d2; o[3]=d3; o[4]=d4; o[5]=d5; o[6]=d6; o[7]=d7; }

//======================================================================

#endif  // Guard
