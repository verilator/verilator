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
/// \brief Verilated DPI header
///
/// This file is included automatically by Verilator at the top of all C++
/// files it generates where DPI is used.  It contains DPI interface
/// functions required by the Verilated code.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_DPI_H_
#define VERILATOR_VERILATED_DPI_H_

#include "verilatedos.h"

#include "verilated.h"  // Also presumably included by caller

#if VM_TIMING == 1
#include "verilated_dpi_call.h"
#else

// Placeholder for compiling with --protect-ids
#define VL_UNKNOWN "<unknown>"

#endif

#include "verilated_sym_props.h"

#include "svdpi.h"

//===================================================================
// SETTING OPERATORS

// Convert svBitVecVal to Verilator internal data
inline void VL_SET_W_SVBV(int obits, WDataOutP owp, const svBitVecVal* lwp) VL_MT_SAFE {
    const int words = VL_WORDS_I(obits);
    for (int i = 0; i < words - 1; ++i) owp[i] = lwp[i];
    owp[words - 1] = lwp[words - 1] & VL_MASK_I(obits);
}
inline void VL_SET_Q_SVBV(int obits, QData& out, const svBitVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_Q(obits) & VL_SET_QII(lwp[1], lwp[0]);
}
inline void VL_SET_I_SVBV(int obits, IData& out, const svBitVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_I(obits) & lwp[0];
}
inline void VL_SET_S_SVBV(int obits, SData& out, const svBitVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_I(obits) & lwp[0];
}
inline void VL_SET_C_SVBV(int obits, CData& out, const svBitVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_I(obits) & lwp[0];
}

// Convert Verilator internal data to svBitVecVal
inline void VL_SET_SVBV_W(int obits, svBitVecVal* owp, const WDataInP lwp) VL_MT_SAFE {
    const int words = VL_WORDS_I(obits);
    for (int i = 0; i < words - 1; ++i) owp[i] = lwp[i];
    owp[words - 1] = lwp[words - 1] & VL_MASK_I(obits);
}
inline void VL_SET_SVBV_I(int, svBitVecVal* owp, const IData ld) VL_MT_SAFE { owp[0] = ld; }
inline void VL_SET_SVBV_Q(int, svBitVecVal* owp, const QData ld) VL_MT_SAFE {
    VL_SET_WQ(WDataOutP::external(owp), ld);
}

// Convert svLogicVecVal to Verilator internal data
// Note these functions ignore X/Z in svLogicVecVal
inline void VL_SET_W_SVLV(int obits, WDataOutP owp, const svLogicVecVal* lwp) VL_MT_SAFE {
    const int words = VL_WORDS_I(obits);
    for (int i = 0; i < words - 1; ++i) owp[i] = lwp[i].aval;
    owp[words - 1] = lwp[words - 1].aval & VL_MASK_I(obits);
}
inline void VL_SET_Q_SVLV(int obits, QData& out, const svLogicVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_Q(obits) & VL_SET_QII(lwp[1].aval, lwp[0].aval);
}
inline void VL_SET_I_SVLV(int obits, IData& out, const svLogicVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_I(obits) & lwp[0].aval;
}
inline void VL_SET_S_SVLV(int obits, SData& out, const svLogicVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_I(obits) & lwp[0].aval;
}
inline void VL_SET_C_SVLV(int obits, CData& out, const svLogicVecVal* lwp) VL_MT_SAFE {
    out = VL_MASK_I(obits) & lwp[0].aval;
}

// Convert Verilator internal data to svLogicVecVal
// Note these functions never create X/Z in svLogicVecVal
inline void VL_SET_SVLV_W(int obits, svLogicVecVal* owp, const WDataInP lwp) VL_MT_SAFE {
    const int words = VL_WORDS_I(obits);
    for (int i = 0; i < words; ++i) owp[i].bval = 0;
    for (int i = 0; i < words - 1; ++i) owp[i].aval = lwp[i];
    owp[words - 1].aval = lwp[words - 1] & VL_MASK_I(obits);
}
inline void VL_SET_SVLV_I(int, svLogicVecVal* owp, const IData ld) VL_MT_SAFE {
    owp[0].aval = ld;
    owp[0].bval = 0;
}
inline void VL_SET_SVLV_Q(int, svLogicVecVal* owp, const QData ld) VL_MT_SAFE {
    VlWide<2> lwp;
    VL_SET_WQ(lwp, ld);
    owp[0].aval = lwp[0];
    owp[0].bval = 0;
    owp[1].aval = lwp[1];
    owp[1].bval = 0;
}

namespace VerilatedDpi {

//=============================================================================
// VlFunctionContext remembers the currently active imported DPI
// function callsite.

struct VlFunctionContext final {

    // MEMBERS
    const char* m_filename;  // File where the function is declared
    int m_lineno;  // Source code line of the function

    // METHODS
    // Check if we are in imported DPI function context
    bool inFunctionContext() const { return m_filename != nullptr; }
};

// DPI imported function being executed on this thread, defined in verilated_dpi.cpp
extern thread_local VlFunctionContext t_fileline;

template <typename Callable, typename... Args>
decltype(auto) callImportFunction(const char* const filename, int lineno, Callable&& call,
                                  Args&&... args) {
    VL_RESTORER(t_fileline);
    t_fileline.m_filename = filename;
    t_fileline.m_lineno = lineno;
    return call(std::forward<Args>(args)...);
}

template <typename Callable, typename... Args>
void callImportTask(Callable&& call, Args&&... args) {
    static_assert(std::is_same<decltype(call(std::forward<Args>(args)...)), int>::value,
                  "DPI imported tasks should have 'int' return type (IEEE 1800-2023 35.5.4 Import "
                  "declarations)");
    (void)call(std::forward<Args>(args)...);
}

template <typename Callable, typename... Args>
decltype(auto) callExportFunction(Callable&& call, Args&&... args) {
    return call(std::forward<Args>(args)...);
}

#if VM_TIMING == 1

// Resume the DPI call once the exported task completes
inline VlCoroutine resumeDpiCallAfter(VlCoroutine coro, VlDpiCall* callp) {
    // Notify the worker thread through callp in case the process was killed.
    struct VlAbortNotify final {
        VlDpiCall* callp;

        ~VlAbortNotify() {
            if (callp) callp->markAborted();
        }
    } notify{callp};
    co_await coro;

    notify.callp = nullptr;
    callp->handoffWorker();
}

template <typename Callable, typename... Args>
VlCoroutine awaitImportTask(VlProcessRef process, Callable&& call, Args&&... args) {
    VlDpiCall dpiCall{
        std::move(process),
        [&]() { callImportTask(std::forward<Callable>(call), std::forward<Args>(args)...); }};
    dpiCall.handoffWorker();
    co_await dpiCall;
}

#endif

static inline bool exportAborted() {
#if VM_TIMING == 1
    VlDpiCall* const callp = VlDpiCall::current();
    return callp && callp->exportAborted();
#else
    return false;
#endif
}

template <typename Callable, typename... Args>
void callExportTask(Callable&& call, Args&&... args) {
    if (t_fileline.inFunctionContext()) {
        VL_FATAL_MT(t_fileline.m_filename, t_fileline.m_lineno, "",
                    "DPI exported task called from function context");
    }
    if (VL_UNLIKELY(exportAborted())) return;
#if VM_TIMING == 1
    // An exported task with timing is a coroutine. Suspend the DPI call until it completes.
    if VL_CONSTEXPR_CXX17 (std::is_same<decltype(call(std::forward<Args>(args)...)),
                                        VlCoroutine>::value) {
        VlDpiCall* const callp = VlDpiCall::current();
        if (VL_UNLIKELY(!callp)) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "DPI export with timing invoked outside of a DPI import thread");
        }

        // Call returns on the first delay or event control
        VlCoroutine coro{call(std::forward<Args>(args)...)};
        if (!coro.await_ready()) {
            resumeDpiCallAfter(std::move(coro), callp);
            VlDpiCall::stopWorker();
        }
        return;
    }
#endif
    call(std::forward<Args>(args)...);
}

};  //namespace VerilatedDpi

//======================================================================

#endif  // Guard
