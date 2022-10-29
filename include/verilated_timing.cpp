// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilated timing implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use timing features.
///
/// See the internals documentation docs/internals.rst for details.
///
//=========================================================================

#include "verilated_timing.h"

//======================================================================
// VlCoroutineHandle:: Methods

void VlCoroutineHandle::resume() {
    // Only null if we have a fork..join_any and one of the other child processes resumed the
    // main process
    if (VL_LIKELY(m_coro)) {
        VL_DEBUG_IF(VL_DBG_MSGF("             Resuming: "); dump(););
        m_coro();
        m_coro = nullptr;
    }
}

#ifdef VL_DEBUG
void VlCoroutineHandle::dump() const {
    VL_PRINTF("Process waiting at %s:%d\n", m_fileline.filename(), m_fileline.lineno());
}
#endif

//======================================================================
// VlDelayScheduler:: Methods

#ifdef VL_DEBUG
void VlDelayScheduler::VlDelayedCoroutine::dump() const {
    VL_DBG_MSGF("             Awaiting time %" PRIu64 ": ", m_timestep);
    m_handle.dump();
}
#endif

void VlDelayScheduler::resume() {
#ifdef VL_DEBUG
    VL_DEBUG_IF(dump(); VL_DBG_MSGF("         Resuming delayed processes\n"););
#endif
    while (awaitingCurrentTime()) {
        if (m_queue.front().m_timestep != m_context.time()) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "%Error: Encountered process that should've been resumed at an "
                        "earlier simulation time. Missed a time slot?");
        }
        // Move max element in the heap to the end
        std::pop_heap(m_queue.begin(), m_queue.end());
        VlCoroutineHandle handle = std::move(m_queue.back().m_handle);
        m_queue.pop_back();
        handle.resume();
    }
}

uint64_t VlDelayScheduler::nextTimeSlot() const {
    if (empty()) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: There is no next time slot scheduled");
    }
    return m_queue.front().m_timestep;
}

#ifdef VL_DEBUG
void VlDelayScheduler::dump() const {
    if (m_queue.empty()) {
        VL_DBG_MSGF("         No delayed processes:\n");
    } else {
        VL_DBG_MSGF("         Delayed processes:\n");
        for (const auto& susp : m_queue) susp.dump();
    }
}
#endif

//======================================================================
// VlTriggerScheduler:: Methods

void VlTriggerScheduler::resume(const char* eventDescription) {
#ifdef VL_DEBUG
    VL_DEBUG_IF(dump(eventDescription);
                VL_DBG_MSGF("         Resuming processes waiting for %s\n", eventDescription););
#endif
    for (auto& susp : m_ready) susp.resume();
    m_ready.clear();
    commit(eventDescription);
}

void VlTriggerScheduler::commit(const char* eventDescription) {
#ifdef VL_DEBUG
    if (!m_uncommitted.empty()) {
        VL_DEBUG_IF(
            VL_DBG_MSGF("         Committing processes waiting for %s:\n", eventDescription);
            for (const auto& susp
                 : m_uncommitted) {
                VL_DBG_MSGF("           - ");
                susp.dump();
            });
    }
#endif
    m_ready.reserve(m_ready.size() + m_uncommitted.size());
    m_ready.insert(m_ready.end(), std::make_move_iterator(m_uncommitted.begin()),
                   std::make_move_iterator(m_uncommitted.end()));
    m_uncommitted.clear();
}

#ifdef VL_DEBUG
void VlTriggerScheduler::dump(const char* eventDescription) const {
    if (m_ready.empty()) {
        VL_DBG_MSGF("         No ready processes waiting for %s\n", eventDescription);
    } else {
        for (const auto& susp : m_ready) {
            VL_DBG_MSGF("         Ready processes waiting for %s:\n", eventDescription);
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
    if (!m_uncommitted.empty()) {
        VL_DBG_MSGF("         Uncommitted processes waiting for %s:\n", eventDescription);
        for (const auto& susp : m_uncommitted) {
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
}
#endif

//======================================================================
// VlDynamicTriggerScheduler:: Methods

bool VlDynamicTriggerScheduler::evaluate() {
    VL_DEBUG_IF(dump(););
    std::swap(m_suspended, m_evaluated);
    for (auto& coro : m_evaluated) coro.resume();
    m_evaluated.clear();
    return !m_triggered.empty();
}

void VlDynamicTriggerScheduler::doPostUpdates() {
    VL_DEBUG_IF(if (!m_post.empty())
                    VL_DBG_MSGF("         Doing post updates for processes:\n");  //
                for (const auto& susp
                     : m_post) {
                    VL_DBG_MSGF("           - ");
                    susp.dump();
                });
    for (auto& coro : m_post) coro.resume();
    m_post.clear();
}

void VlDynamicTriggerScheduler::resume() {
    VL_DEBUG_IF(if (!m_triggered.empty()) VL_DBG_MSGF("         Resuming processes:\n");  //
                for (const auto& susp
                     : m_triggered) {
                    VL_DBG_MSGF("           - ");
                    susp.dump();
                });
    for (auto& coro : m_triggered) coro.resume();
    m_triggered.clear();
}

#ifdef VL_DEBUG
void VlDynamicTriggerScheduler::dump() const {
    if (m_suspended.empty()) {
        VL_DBG_MSGF("         No suspended processes waiting for dynamic trigger evaluation\n");
    } else {
        for (const auto& susp : m_suspended) {
            VL_DBG_MSGF("         Suspended processes waiting for dynamic trigger evaluation:\n");
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
}
#endif

//======================================================================
// VlForkSync:: Methods

void VlForkSync::done(const char* filename, int lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("             Process forked at %s:%d finished\n", filename, lineno););
    if (m_join->m_counter > 0) m_join->m_counter--;
    if (m_join->m_counter == 0) m_join->m_susp.resume();
}

//======================================================================
// VlCoroutine:: Methods

VlCoroutine::VlPromise::~VlPromise() {
    // Indicate to the return object that the coroutine has finished or been destroyed
    if (m_corop) m_corop->m_promisep = nullptr;
    // If there is a continuation, destroy it
    if (m_continuation) m_continuation.destroy();
}

std::suspend_never VlCoroutine::VlPromise::final_suspend() noexcept {
    // Indicate to the return object that the coroutine has finished
    if (m_corop) {
        m_corop->m_promisep = nullptr;
        // Forget the return value, we won't need it and it won't be able to let us know if
        // it's destroyed
        m_corop = nullptr;
    }
    // If there is a continuation, resume it
    if (m_continuation) {
        m_continuation();
        m_continuation = nullptr;
    }
    return {};
}
