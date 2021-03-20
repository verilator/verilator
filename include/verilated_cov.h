// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Coverage analysis support
///
//=============================================================================

#ifndef VERILATOR_VERILATED_COV_H_
#define VERILATOR_VERILATED_COV_H_

#include "verilatedos.h"
#include "verilated.h"

#include <iostream>
#include <sstream>
#include <string>

class VerilatedCovImp;

//=============================================================================
/// Conditionally compile coverage code

// clang-format off
#ifdef VM_COVERAGE
# define VL_IF_COVER(stmts) \
    do { stmts; } while (false)
#else
# define VL_IF_COVER(stmts) \
    do { \
        if (false) { stmts; } \
    } while (false)
#endif
// clang-format on

//=============================================================================
/// Insert a item for coverage analysis.
/// The first argument is a pointer to the count to be dumped.
/// The remaining arguments occur in pairs: A string key, and a value.
/// The value may be a string, or another type which will be auto-converted to a string.
///
/// Some typical keys:
///     filename        File the recording occurs in.  Defaults to __FILE__
///     lineno          Line number the recording occurs in.  Defaults to __LINE__
///     column          Column number (or occurrence# for dup file/lines).  Defaults to undef.
///     hier            Hierarchical name.  Defaults to name()
///     type            Type of coverage.  Defaults to "user"
///                     Other types are 'block', 'fsm', 'toggle'.
///     comment         Description of the coverage event.  Should be set by the user.
///                     Comments for type==block: 'if', 'else', 'elsif', 'case'
///     thresh          Threshold to consider fully covered.
///                     If unspecified, downstream tools will determine it.
///
/// Examples:
///
///     vluint32_t m_cases[10];
///     constructor {
///         for (int i=0; i<10; ++i) { m_cases[i]=0; }
///     }
///     for (int i=0; i<10; ++i) {
///             VL_COVER_INSERT(&m_cases[i], "comment", "Coverage Case", "i", cvtToNumStr(i));
///     }

#define VL_COVER_INSERT(covcontextp, countp, ...) \
    VL_IF_COVER(covcontextp->_inserti(countp); covcontextp->_insertf(__FILE__, __LINE__); \
                covcontextp->_insertp("hier", name(), __VA_ARGS__))

//=============================================================================
/// Convert VL_COVER_INSERT value arguments to strings

template <class T> std::string vlCovCvtToStr(const T& t) VL_PURE {
    std::ostringstream os;
    os << t;
    return os.str();
}

//=============================================================================
//  VerilatedCov
///  Verilator coverage per-context structure
/// All public methods in this class are thread safe.

class VerilatedCovContext VL_NOT_FINAL : public VerilatedVirtualBase {
    VL_UNCOPYABLE(VerilatedCovContext);

public:
    // METHODS
    /// Return default filename
    static const char* defaultFilename() VL_PURE { return "coverage.dat"; }
    /// Write all coverage data to a file
    void write(const char* filenamep = defaultFilename()) VL_MT_SAFE;
    /// Clear coverage points (and call delete on all items)
    void clear() VL_MT_SAFE;
    /// Clear items not matching the provided string
    void clearNonMatch(const char* matchp) VL_MT_SAFE;
    /// Zero coverage points
    void zero() VL_MT_SAFE;

public:  // But Internal use only
    /// Insert a coverage item
    /// We accept from 1-30 key/value pairs, all as strings.
    /// Call _insert1, followed by _insert2 and _insert3
    /// Do not call directly; use VL_COVER_INSERT or higher level macros instead
    // _insert1: Remember item pointer with count.  (Not const, as may add zeroing function)
    void _inserti(vluint32_t* itemp) VL_MT_SAFE;
    void _inserti(vluint64_t* itemp) VL_MT_SAFE;
    // _insert2: Set default filename and line number
    void _insertf(const char* filename, int lineno) VL_MT_SAFE;
    // _insert3: Set parameters
    // We could have just the maximum argument version, but this compiles
    // much slower (nearly 2x) than having smaller versions also.  However
    // there's not much more gain in having a version for each number of args.
#define K(n) const char* key##n
#define A(n) const char *key##n, const char *valp##n  // Argument list
#define D(n) const char *key##n = nullptr, const char *valp##n = nullptr  // Argument list
    void _insertp(D(0), D(1), D(2), D(3), D(4), D(5), D(6), D(7), D(8), D(9));
    void _insertp(A(0), A(1), A(2), A(3), A(4), A(5), A(6), A(7), A(8), A(9), A(10), D(11), D(12),
                  D(13), D(14), D(15), D(16), D(17), D(18), D(19));
    void _insertp(A(0), A(1), A(2), A(3), A(4), A(5), A(6), A(7), A(8), A(9), A(10), A(11), A(12),
                  A(13), A(14), A(15), A(16), A(17), A(18), A(19), A(20), D(21), D(22), D(23),
                  D(24), D(25), D(26), D(27), D(28), D(29));
    // Backward compatibility for Verilator
    void _insertp(A(0), A(1), K(2), int val2, K(3), int val3, K(4), const std::string& val4, A(5),
                  A(6), A(7));

#undef K
#undef A
#undef D

protected:
    friend class VerilatedCovImp;
    // CONSTRUCTORS
    // Internal: Only made as part of VerilatedCovImp
    VerilatedCovContext() {}
    virtual ~VerilatedCovContext() {}

    // METHODS
    // Internal: access to implementation class
    VerilatedCovImp* impp() { return reinterpret_cast<VerilatedCovImp*>(this); }
};

//=============================================================================
//  VerilatedCov
///  Verilator coverage global class
///
/// Global class that accesses via current thread's context.  These are
/// provided for backward-compatibility, use VerilatedContext->coveragep()
/// instead.

#ifndef VL_NO_LEGACY
class VerilatedCov final {
    VL_UNCOPYABLE(VerilatedCov);

public:
    // METHODS
    /// Return default filename for the current thread
    static const char* defaultFilename() VL_PURE { return VerilatedCovContext::defaultFilename(); }
    /// Write all coverage data to a file for the current thread
    static void write(const char* filenamep = defaultFilename()) VL_MT_SAFE {
        threadCovp()->write(filenamep);
    }
    /// Clear coverage points (and call delete on all items) for the current thread
    static void clear() VL_MT_SAFE { threadCovp()->clear(); }
    /// Clear items not matching the provided string for the current thread
    static void clearNonMatch(const char* matchp) VL_MT_SAFE {
        threadCovp()->clearNonMatch(matchp);
    }
    /// Zero coverage points for the current thread
    static void zero() VL_MT_SAFE { threadCovp()->zero(); }

private:
    /// Current thread's coverage structure
    static VerilatedCovContext* threadCovp() VL_MT_SAFE;
};
#endif

#endif  // Guard
