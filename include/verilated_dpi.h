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
#include "verilated_fiber.h"
#include "verilated_timing.h"

#include <coroutine>
#else

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

namespace {
static thread_local struct {
    std::string m_filename{};
    int m_lineno{};
    bool m_inFuncContext{false};
} s_fileline;
};  //namespace

template <bool isTask, typename Callable, typename... Args>
decltype(auto) callImport(const char* const filename, int lineno, Callable&& call,
                          Args&&... args) {
    if VL_CONSTEXPR_CXX17 (!isTask) {
        s_fileline.m_inFuncContext = true;
        s_fileline.m_filename = std::string{filename};
        s_fileline.m_lineno = lineno;
    }
    if VL_CONSTEXPR_CXX17 (std::is_same<decltype(call(std::forward<Args>(args)...)),
                                        void>::value) {
        call(std::forward<Args>(args)...);
        s_fileline.m_inFuncContext = false;
    } else {
        auto ret = call(std::forward<Args>(args)...);
        s_fileline.m_inFuncContext = false;
        return ret;
    }
}

template <bool isTask, typename Callable, typename... Args>
decltype(auto) awaitExport(Callable&& call, Args&&... args) {
    if VL_CONSTEXPR_CXX17 (isTask) {
        if (s_fileline.m_inFuncContext) {
            VL_FATAL_MT(s_fileline.m_filename.c_str(), s_fileline.m_lineno, "",
                        "DPI exported task called from function context");
        }
    }

    if VL_CONSTEXPR_CXX17 (std::is_same<decltype(call(std::forward<Args>(args)...)),
                                        void>::value) {
        call(std::forward<Args>(args)...);
    } else {
        return call(std::forward<Args>(args)...);
    }
}

#if VM_TIMING == 1

namespace {
class FiberAwaitable final {
    VlFiber& m_fiber;

public:
    explicit FiberAwaitable(VlFiber& fiber)
        : m_fiber{fiber} {}

    bool await_ready() const noexcept { return m_fiber.isDone(); }
    void await_suspend(std::coroutine_handle<> waiter) const { m_fiber.setWaiter(waiter); }
    void await_resume() const noexcept {}
};
};  //namespace

// Run user C code in a fiber, wrapping it in a coroutine for scheduler integration
// This allows the C code to call DPI exports with timing controls
// Callable has void return type because it is a task.
template <typename Callable, typename... Args>
VlCoroutine callImportFiber(Callable&& call, Args&&... args) {
    static_assert(std::is_same<decltype(call(std::forward<Args>(args)...)), int>::value,
                  "Functions called inside a fiber should have 'int' return type");
    auto fiberp{VlFiber::create(
        [&call, &args...]() mutable { std::ignore = call(std::forward<Args>(args)...); })};
    while (!fiberp->isDone()) {
        fiberp->resume();
        co_await FiberAwaitable{*fiberp};
    }
    co_return;
}

// Suspend the current fiber until the DPI export coroutine completes
// Must be called from within a fiber context (i.e., from C code called via DPI import)
template <typename Callable, typename... Args>
decltype(auto) awaitExportFiber(Callable&& call, Args&&... args) {
    if VL_CONSTEXPR_CXX17 (std::is_same<decltype(call(std::forward<Args>(args)...)),
                                        VlCoroutine>::value) {
        if (s_fileline.m_inFuncContext) {
            VL_FATAL_MT(s_fileline.m_filename.c_str(), s_fileline.m_lineno, "",
                        "DPI exported task called from function context");
        }
        VlFiber* fiberp = VlFiber::current();
        if (VL_UNLIKELY(!fiberp)) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "DPI export with timing invoked outside of a fiber context");
        }
        VlCoroutine continuation = [=]() mutable -> VlCoroutine {
            // Save fiber pointer
            VlFiber* f = fiberp;

            // Use std::suspend_always, so that fiber resumption
            // is invoked once exported function finishes
            co_await std::suspend_always{};
            f->resume();
            co_return;
        }();
        // Call will return on first delay/event encountered
        VlCoroutine local{call(std::forward<Args>(args)...)};
        if (!local.await_ready()) {
            local.setFiberContinuation(&continuation);
            while (!local.await_ready()) { VlFiber::yield(); }
        }
    } else if (std::is_same<decltype(call(std::forward<Args>(args)...)), void>::value) {
        return call(std::forward<Args>(args)...);
    } else {
        call(std::forward<Args>(args)...);
    }
}

#endif

};  //namespace VerilatedDpi

//======================================================================

#endif  // Guard
