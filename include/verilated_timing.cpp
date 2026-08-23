// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
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
        if (m_process) {  // If process state is managed with std::process
            if (m_process->state() == VlProcess::KILLED) {
                m_coro.destroy();
            } else {
                m_process->state(VlProcess::RUNNING);
                VlProcess::currentp(m_process.get());
                m_coro();
                VlProcess::currentp(nullptr);
            }
        } else {
            VlProcess::currentp(nullptr);
            m_coro();
        }
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

void VlDelayScheduler::resume() {
#ifdef VL_DEBUG
    VL_DEBUG_IF(dump(); VL_DBG_MSGF("         Resuming delayed processes\n"););
#endif
    if (VL_UNLIKELY(m_context.gotFinish())) {  // LCOV_EXCL_START: Direct calls after finish only
        for (Queue& queue : m_queues) {
            queue.m_delayed.clear();
            queue.m_zeroDelayed.clear();
        }
        m_zeroDelayesSwap.clear();
        return;
    }  // LCOV_EXCL_STOP
    bool resumed = false;
    VlDelayedCoroutineQueue& queue = m_queues[m_context.inReactive()].m_delayed;

    while (!queue.empty() && (queue.cbegin()->first == m_context.time())) {
        VlCoroutineHandle handle = std::move(queue.begin()->second);
        queue.erase(queue.begin());
        handle.resume();
        resumed = true;
    }

    if (!resumed) {
        if (m_context.time() == 0) {
            // Nothing was scheduled at time 0, but resume() got called due to --x-initial-edge
            return;
        }

        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "%Error: Encountered process that should've been resumed at an "
                    "earlier simulation time. Missed a time slot?\n");
    }
}

void VlDelayScheduler::resumeZeroDelay() {
    std::vector<VlCoroutineHandle>& zeroDelayed = m_queues[m_context.inReactive()].m_zeroDelayed;
    if (VL_UNLIKELY(m_context.gotFinish())) {  // LCOV_EXCL_START: Direct calls after finish only
        zeroDelayed.clear();
        m_zeroDelayesSwap.clear();
        return;
    }  // LCOV_EXCL_STOP
    m_zeroDelayesSwap.swap(zeroDelayed);
    for (VlCoroutineHandle& handle : m_zeroDelayesSwap) handle.resume();
    m_zeroDelayesSwap.clear();
}

uint64_t VlDelayScheduler::nextTimeSlot() const {
    if (!m_queues[0].m_zeroDelayed.empty() || !m_queues[1].m_zeroDelayed.empty()) {
        return m_context.time();  // LCOV_EXCL_LINE: Eval drains #0 queues before returning
    }
    const VlDelayedCoroutineQueue& active = m_queues[0].m_delayed;
    const VlDelayedCoroutineQueue& reactive = m_queues[1].m_delayed;
    if (!active.empty() && !reactive.empty()) {
        return std::min(active.cbegin()->first, reactive.cbegin()->first);
    }
    if (!active.empty()) return active.cbegin()->first;
    if (!reactive.empty()) return reactive.cbegin()->first;
    VL_FATAL_MT(__FILE__, __LINE__, "", "There is no next time slot scheduled");
    VL_UNREACHABLE;
}

#ifdef VL_DEBUG
void VlDelayScheduler::dump() const {
    const Queue& queue = m_queues[m_context.inReactive()];
    if (queue.m_delayed.empty() && queue.m_zeroDelayed.empty()) {
        VL_DBG_MSGF("         No delayed processes:\n");
    } else {
        VL_DBG_MSGF("         Delayed processes:\n");
        for (const auto& susp : queue.m_zeroDelayed) {
            VL_DBG_MSGF("             Awaiting #0-delayed resumption, "
                        "time () %" PRIu64 ": ",
                        m_context.time());
            susp.dump();
        }
        for (const auto& susp : queue.m_delayed) {
            VL_DBG_MSGF("             Awaiting time %" PRIu64 ": ", susp.first);
            susp.second.dump();
        }
    }
}
#endif

//======================================================================
// VlTriggerScheduler:: Methods

void VlTriggerScheduler::resume(const char* eventDescription, bool reactive) {
#ifdef VL_DEBUG
    VL_DEBUG_IF(dump(eventDescription, reactive);
                VL_DBG_MSGF("         Resuming processes waiting for %s\n", eventDescription););
#endif
    Queue& queue = m_queues[reactive];
    if (VL_UNLIKELY(Verilated::threadContextp()->gotFinish())) {
        queue.m_toResume.clear();
        queue.m_fired.clear();
        queue.m_awaiting.clear();
        return;
    }
    for (VlCoroutineHandle& coro : queue.m_toResume) coro.resume();
    queue.m_toResume.clear();
}

void VlTriggerScheduler::moveToResumeQueue(const char* eventDescription, bool reactive) {
    Queue& queue = m_queues[reactive];
#ifdef VL_DEBUG
    if (!queue.m_fired.empty()) {
        VL_DEBUG_IF(VL_DBG_MSGF("         Moving to resume queue processes waiting for %s:\n",
                                eventDescription);
                    for (const auto& susp
                         : queue.m_fired) {
                        VL_DBG_MSGF("           - ");
                        susp.dump();
                    });
    }
#endif
    if (VL_UNLIKELY(Verilated::threadContextp()->gotFinish())) {
        queue.m_toResume.clear();
        queue.m_fired.clear();
        return;
    }
    std::swap(queue.m_fired, queue.m_toResume);
}

void VlTriggerScheduler::ready(const char* eventDescription) {
    for (Queue& queue : m_queues) {
#ifdef VL_DEBUG
        if (!queue.m_awaiting.empty()) {
            VL_DEBUG_IF(
                VL_DBG_MSGF("         Committing processes waiting for %s:\n", eventDescription);
                for (const auto& susp
                     : queue.m_awaiting) {
                    VL_DBG_MSGF("           - ");
                    susp.dump();
                });
        }
#endif
        if (VL_UNLIKELY(Verilated::threadContextp()->gotFinish())) {
            queue.m_fired.clear();
            queue.m_awaiting.clear();
            continue;
        }
        const size_t expectedSize = queue.m_fired.size() + queue.m_awaiting.size();
        if (queue.m_fired.capacity() < expectedSize) queue.m_fired.reserve(expectedSize * 2);
        queue.m_fired.insert(queue.m_fired.end(),
                             std::make_move_iterator(queue.m_awaiting.begin()),
                             std::make_move_iterator(queue.m_awaiting.end()));
        queue.m_awaiting.clear();
    }
}

#ifdef VL_DEBUG
void VlTriggerScheduler::dump(const char* eventDescription, bool reactive) const {
    const Queue& queue = m_queues[reactive];
    if (queue.m_toResume.empty()) {
        VL_DBG_MSGF("         No process to resume waiting for %s\n", eventDescription);
    } else {
        for (const auto& susp : queue.m_toResume) {
            VL_DBG_MSGF("         Processes to resume waiting for %s:\n", eventDescription);
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
    if (!queue.m_fired.empty()) {
        VL_DBG_MSGF("         Triggered processes waiting for %s:\n", eventDescription);
        for (const auto& susp : queue.m_fired) {
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
    if (!queue.m_awaiting.empty()) {
        VL_DBG_MSGF("         Not triggered processes waiting for %s:\n", eventDescription);
        for (const auto& susp : queue.m_awaiting) {
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
}
#endif

//======================================================================
// VlDynamicTriggerScheduler:: Methods

bool VlDynamicTriggerScheduler::evaluate() {
    VerilatedContext* const contextp = Verilated::threadContextp();
    if (VL_UNLIKELY(contextp->gotFinish())) {
        m_anyTriggered = false;
        for (VlCoroutineVec& queue : m_suspended) queue.clear();
        m_evaluated.clear();
        for (VlCoroutineVec& queue : m_triggered) queue.clear();
        for (VlCoroutineVec& queue : m_post) queue.clear();
        return false;
    }
    m_anyTriggered = false;
    VL_DEBUG_IF(dump(););
    const bool inReactive = contextp->inReactive();
    for (unsigned region = 0; region < m_suspended.size(); ++region) {
        // Trigger evaluation must retain the waiting thread's region across its synthetic awaits.
        contextp->inReactive(region != 0);
        std::swap(m_suspended[region], m_evaluated);
        for (VlCoroutineHandle& coro : m_evaluated) coro.resume();
        m_evaluated.clear();
    }
    contextp->inReactive(inReactive);
    return m_anyTriggered;
}

void VlDynamicTriggerScheduler::doPostUpdates() {
    VerilatedContext* const contextp = Verilated::threadContextp();
    const bool inReactive = contextp->inReactive();
    for (unsigned region = 0; region < m_post.size(); ++region) {
        VlCoroutineVec& post = m_post[region];
        contextp->inReactive(region != 0);
        VL_DEBUG_IF(if (!post.empty())
                        VL_DBG_MSGF("         Doing post updates for processes:\n");  //
                    for (const auto& susp
                         : post) {
                        VL_DBG_MSGF("           - ");
                        susp.dump();
                    });
        if (VL_UNLIKELY(contextp->gotFinish())) {
            post.clear();
            continue;
        }
        for (VlCoroutineHandle& coro : post) coro.resume();
        post.clear();
    }
    contextp->inReactive(inReactive);
}

void VlDynamicTriggerScheduler::resume() {
    VlCoroutineVec& triggered = m_triggered[Verilated::threadContextp()->inReactive()];
    VL_DEBUG_IF(if (!triggered.empty()) VL_DBG_MSGF("         Resuming processes:\n");  //
                for (const auto& susp
                     : triggered) {
                    VL_DBG_MSGF("           - ");
                    susp.dump();
                });
    if (VL_UNLIKELY(Verilated::threadContextp()->gotFinish())) {
        triggered.clear();
        return;
    }
    for (VlCoroutineHandle& coro : triggered) coro.resume();
    triggered.clear();
}

#ifdef VL_DEBUG
void VlDynamicTriggerScheduler::dump() const {
    const VlCoroutineVec& suspended = m_suspended[Verilated::threadContextp()->inReactive()];
    if (suspended.empty()) {
        VL_DBG_MSGF("         No suspended processes waiting for dynamic trigger evaluation\n");
    } else {
        for (const auto& susp : suspended) {
            VL_DBG_MSGF("         Suspended processes waiting for dynamic trigger evaluation:\n");
            VL_DBG_MSGF("           - ");
            susp.dump();
        }
    }
}
#endif

//======================================================================
// VlForkSync:: Methods

void VlProcess::forkSyncOnKill(std::shared_ptr<VlForkSyncState> forkSyncp) {
    m_forkSyncOnKillp = forkSyncp;
    m_forkSyncOnKillDone = false;
}

void VlProcess::forkSyncOnKillClear(VlForkSyncState* forkSyncp) {
    if (m_forkSyncOnKillp.get() != forkSyncp) return;
    m_forkSyncOnKillp = nullptr;
    m_forkSyncOnKillDone = false;
}

void VlProcess::state(int s) {
    if (s == KILLED && m_state != KILLED && m_state != FINISHED && m_forkSyncOnKillp
        && !m_forkSyncOnKillDone) {
        m_forkSyncOnKillDone = true;
        m_state = s;
        m_forkSyncOnKillp->done();
        m_forkSyncOnKillp = nullptr;
        return;
    }
    m_state = s;
}

void VlForkSync::onKill(VlProcessRef process) {
    if (!process) return;
    process->forkSyncOnKill(m_state);
}

void VlForkSyncState::done(const char* filename, int lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("             Process forked at %s:%d finished\n", filename, lineno););
    if (!m_inited) {
        ++m_pendingDones;
        return;
    }
    if (m_counter > 0) m_counter--;
    if (m_counter != 0) return;
    if (m_inDone) {
        m_resumePending = true;
        return;
    }
    m_inDone = true;
    do {
        m_resumePending = false;
        m_susp.resume();
    } while (m_resumePending && m_inited && m_counter == 0);
    m_inDone = false;
}

//======================================================================
// VlPromise:: Methods

VlCoroutine VlPromise::get_return_object() { return {this}; }

VlPromise::~VlPromise() {
    // Indicate to the return object that the coroutine has finished or been destroyed
    if (m_corop) m_corop->m_promisep = nullptr;
    // If there is a continuation, destroy it
    if (m_continuation) m_continuation.destroy();
}

std::suspend_never VlPromise::final_suspend() noexcept {
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
