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
//*************************************************************************
///
/// \file
/// \brief Verilated timing header
///
/// This file is included automatically by Verilator in some of the C++ files
/// it generates if timing features are used.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
/// See the internals documentation docs/internals.rst for details.
///
//*************************************************************************
#ifndef VERILATOR_VERILATED_TIMING_H_
#define VERILATOR_VERILATED_TIMING_H_

#include "verilated.h"

#include <limits>
#include <map>
#include <utility>
#include <vector>

// clang-format off
// Some preprocessor magic to support both Clang and GCC coroutines with both libc++ and libstdc++
#ifdef _LIBCPP_VERSION  // libc++
# if defined(__has_include) && !__has_include(<coroutine>) && __has_include(<experimental/coroutine>)
#  if __clang_major__ > 13  // Clang > 13 warns that coroutine types in std::experimental are deprecated
#   pragma clang diagnostic push
#   pragma clang diagnostic ignored "-Wdeprecated-experimental-coroutine"
#  endif
#  include <experimental/coroutine>
   namespace std {
       using namespace experimental;  // Bring std::experimental into the std namespace
   }
# else
#  include <coroutine>
# endif
#else
# if defined __clang__ && defined __GLIBCXX__ && !defined __cpp_impl_coroutine
#  define __cpp_impl_coroutine 1  // Clang doesn't define this, but it's needed for libstdc++
# endif
# include <coroutine>
# if __clang_major__ < 14
   namespace std {  // Bring coroutine library into std::experimental, as Clang < 14 expects it to be there
       namespace experimental {
           using namespace std;
       }
   }
# endif
#endif
// clang-format on

// Placeholder for compiling with --protect-ids
#define VL_UNKNOWN "<unknown>"

//=============================================================================
// VlCoroutineHandle is a non-copyable (but movable) coroutine handle. On resume, the handle is
// cleared, as we assume that either the coroutine has finished and deleted itself, or, if it got
// suspended, another VlCoroutineHandle was created to manage it.
//
// m_processp is a non-owning raw pointer. The coroutine frame's VlProcessRef (shared_ptr)
// owns the VlProcess for the frame's lifetime; queue/scheduler moves must not bump that
// refcount. resume() nulls m_processp with m_coro. Fork init may hold a null-coro handle
// that only marks WAITING. Await APIs take const VlProcessRef& and store .get().

class VlCoroutine;

struct VlPromise final {
    std::coroutine_handle<VlPromise>
        m_continuation;  // Coroutine to resume after this one finishes
    VlCoroutine* m_corop = nullptr;  // Pointer to the coroutine return object
    bool m_forever = false;  // Coroutine suspended forever

    ~VlPromise();

    VlCoroutine get_return_object();

    // Never suspend at the start of the coroutine
    std::suspend_never initial_suspend() const { return {}; }

    // Never suspend at the end of the coroutine (thanks to this, the coroutine will clean up
    // after itself)
    std::suspend_never final_suspend() noexcept;

    void unhandled_exception() const { std::abort(); }  // LCOV_EXCL_LINE
    void return_void() const {}
};

class VlCoroutineHandle final {
    VL_UNCOPYABLE(VlCoroutineHandle);

    // MEMBERS
    std::coroutine_handle<VlPromise> m_coro;  // The wrapped coroutine handle
    VlProcess* m_processp;  // Non-owning; null if process state unused
    VlFileLineDebug m_fileline;  // Source location, for debug

public:
    // CONSTRUCTORS
    // Construct
    // non-explicit:
    // cppcheck-suppress noExplicitConstructor
    VlCoroutineHandle(VlProcess* processp)
        : m_coro{nullptr}
        , m_processp{processp} {
        if (m_processp) m_processp->state(VlProcess::WAITING);
    }
    VlCoroutineHandle(std::coroutine_handle<VlPromise> coro, VlProcess* processp,
                      VlFileLineDebug fileline)
        : m_coro{coro}
        , m_processp{processp}
        , m_fileline{fileline} {
        if (m_processp) m_processp->state(VlProcess::WAITING);
    }
    // Move the handle, leaving a nullptr
    // non-explicit:
    // cppcheck-suppress noExplicitConstructor
    VlCoroutineHandle(VlCoroutineHandle&& moved)
        : m_coro{std::exchange(moved.m_coro, nullptr)}
        , m_processp{std::exchange(moved.m_processp, nullptr)}
        , m_fileline{moved.m_fileline} {}
    // Destroy if the handle isn't null
    ~VlCoroutineHandle() {
        // Usually these coroutines should get resumed; we only need to clean up if we destroy a
        // model with some coroutines suspended
        if (VL_UNLIKELY(m_coro)) {
            if (m_processp && m_processp->state() != VlProcess::KILLED
                && !m_coro.promise().m_forever) {
                m_processp->state(VlProcess::FINISHED);
            }
            m_coro.destroy();
        }
    }
    // METHODS
    // Move the handle, leaving a null handle
    auto& operator=(VlCoroutineHandle&& moved) {
        m_coro = std::exchange(moved.m_coro, nullptr);
        m_processp = std::exchange(moved.m_processp, nullptr);
        m_fileline = moved.m_fileline;
        return *this;
    }
    // Resume the coroutine if the handle isn't null and the process isn't killed
    void resume();
#ifdef VL_DEBUG
    void dump() const;
#endif
};

enum class VlDelayPhase : bool { ACTIVE, INACTIVE };

//=============================================================================
// VlDelayedCoroutineQueue -- time-ordered FIFO buckets of delayed coroutines.
//
// Why not std::multimap: equal-time inserts sift handles through the tree.
// One map node per distinct time; FIFO within the bucket. After drain, the
// vector is kept as one spare for the next multi-waiter time slot.
//
// drainTop erases the map node before resumes run so a same-time re-await
// creates a new entry (must not append into the bucket being drained).
// C++14: no std::optional / map::extract (covergroup tests force -std=c++14).

class VlDelayedCoroutineQueue final {
    using RestVec = std::vector<VlCoroutineHandle>;

    struct Bucket final {
        RestVec m_handles;  // FIFO waiters at this time (size >= 1 while mapped)
    };

    std::map<uint64_t, Bucket> m_map;  // Time -> waiters
    RestVec m_spareRest;  // At most one recycled waiter vector

    void ensureHandles(Bucket& bucket) {
        if (bucket.m_handles.capacity() != 0) return;
        if (m_spareRest.capacity() != 0) bucket.m_handles = std::move(m_spareRest);
    }
    void recycleHandles(Bucket& bucket) {
        if (bucket.m_handles.capacity() == 0) return;
        bucket.m_handles.clear();
        m_spareRest = std::move(bucket.m_handles);
    }

public:
    bool empty() const { return m_map.empty(); }
    // Called from resume() only when gotFinish is already set. Delay trigger
    // evaluation is gated on !gotFinish, so this is a rare safety path.
    void clear() {  // LCOV_EXCL_START
        m_map.clear();
        m_spareRest.clear();
    }  // LCOV_EXCL_STOP
    uint64_t topTime() const { return m_map.begin()->first; }
    void emplace(uint64_t time, VlCoroutineHandle&& handle) {
        Bucket& bucket = m_map[time];
        ensureHandles(bucket);
        bucket.m_handles.push_back(std::move(handle));
    }
    template <typename T_Func>
    void drainTop(T_Func&& func) {
        auto it = m_map.begin();
        Bucket bucket = std::move(it->second);
        m_map.erase(it);
        for (VlCoroutineHandle& handle : bucket.m_handles) func(handle);
        recycleHandles(bucket);
    }
#ifdef VL_DEBUG
    template <typename T_Func>
    void foreachInOrder(T_Func&& func) const {
        for (const auto& pair : m_map) {
            for (const VlCoroutineHandle& handle : pair.second.m_handles) {
                func(pair.first, handle);
            }
        }
    }
#endif
};

//=============================================================================
// VlDelayScheduler stores coroutines to be resumed at a certain simulation time. If the current
// time is equal to a coroutine's resume time, the coroutine gets resumed.

class VlDelayScheduler final {
    // MEMBERS
    VerilatedContext& m_context;  // Context to get current time from
    VlDelayedCoroutineQueue m_queue;  // Coroutines to be restored at a certain simulation time
    std::vector<VlCoroutineHandle> m_zeroDelayed;  // Coroutines waiting for #0
    // Coroutines that waited for #0 and are being resumed now. As member to avoid reallocations
    std::vector<VlCoroutineHandle> m_zeroDelayesSwap;
    std::vector<VlCoroutineHandle>
        m_forevered;  // Coroutines, that called wait(0), and are to be freed.
    // Their callers are freed recursively through m_continuation.
    //
    // NOTE: it would be possible to clean up forevered coroutines immedietely without storing
    // them, but it involves a lot of nasty edge cases. Defering cleanup to end of eval step
    // simplifies logic a lot by ensuring that whole "coroutine stack" was already suspended.
public:
    // CONSTRUCTORS
    explicit VlDelayScheduler(VerilatedContext& context)
        : m_context{context} {}
    // METHODS
    // Resume coroutines waiting for the current simulation time
    void resume();
    // Resume coroutines waiting for #0
    void resumeZeroDelay();
    // Returns the simulation time of the next time slot (aborts if there are no delayed
    // coroutines)
    uint64_t nextTimeSlot() const;
    // Are there no delayed coroutines awaiting?
    bool empty() const { return m_queue.empty() && m_zeroDelayed.empty(); }
    // Are there coroutines to resume at the current simulation time?
    bool awaitingCurrentTime() const {
        return !m_context.gotFinish()
               && (!m_queue.empty() && (m_queue.topTime() <= m_context.time()));
    }
    // Are there coroutines to resume in the inactive region after a #0 delay?
    bool awaitingZeroDelay() const { return !m_context.gotFinish() && !m_zeroDelayed.empty(); }
    void cleanupForevered() { m_forevered.clear(); };
#ifdef VL_DEBUG
    void dump() const;
#endif
    // Used by coroutines for co_awaiting a certain simulation time
    auto delay(uint64_t delay, const VlProcessRef& process, const char* filename = VL_UNKNOWN,
               int lineno = 0) {
        struct Awaitable final {
            VlProcess* processp;  // Non-owning; null if process state unused
            VlDelayedCoroutineQueue& queue;
            std::vector<VlCoroutineHandle>& queueZeroDelay;
            const uint64_t delay;
            const VlDelayPhase phase;
            const VlFileLineDebug fileline;

            bool await_ready() const { return false; }  // Always suspend
            void await_suspend(std::coroutine_handle<VlPromise> coro) {
                // Active delays and fork..join_none #0 resume from the time queue.
                VlCoroutineHandle handle{coro, processp, fileline};
                if (phase != VlDelayPhase::INACTIVE) {
                    queue.emplace(delay, std::move(handle));
                } else {
                    queueZeroDelay.push_back(std::move(handle));
                }
            }
            void await_resume() const {}
        };

        VlDelayPhase phase;
        if (delay != 0) {
            // UINT64_MAX is a sentinel for synthetic fork..join_none delays.
            if (delay == std::numeric_limits<uint64_t>::max()) delay = 0;
            phase = VlDelayPhase::ACTIVE;
        } else {
            phase = VlDelayPhase::INACTIVE;
        }
        return Awaitable{process.get(), m_queue,
                         m_zeroDelayed, m_context.time() + delay,
                         phase,         VlFileLineDebug{filename, lineno}};
    }

    // Helper awaitable func for suspending coroutines forever.
    // Used for constant wait statements.
    auto waitForever(const VlProcessRef& process, const char* filename = VL_UNKNOWN,
                     int lineno = 0) {
        VL_DEBUG_IF(
            VL_DBG_MSGF("             Awaiting join of fork at: %s:%d\n", filename, lineno););
        struct Awaitable final {
            VlProcess* processp;  // Non-owning; null if process state unused
            std::vector<VlCoroutineHandle>& forevered;
            VlFileLineDebug fileline;

            bool await_ready() { return false; }
            void await_suspend(std::coroutine_handle<VlPromise> coro) {
                coro.promise().m_forever = true;
                forevered.emplace_back(VlCoroutineHandle{coro, processp, fileline});
            }
            void await_resume() const {}  // LCOV_EXCL_LINE
        };
        return Awaitable{process.get(), m_forevered, VlFileLineDebug{filename, lineno}};
    }
};

//=============================================================================
// VlTriggerScheduler stores coroutines to be resumed by a trigger. It does not keep track of its
// trigger, relying on calling code to resume when appropriate. Coroutines are kept in three stages
// - 'awaiting', 'fired' and 'toResume'. Whenever a coroutine is suspended, it lands in the
// 'awaiting' stage. Only when ready() is called, these coroutines get moved to the 'fired' stage.
// When moveToResumeQueue() is begin called all coroutines from 'ready' are moved to 'toResume'.
// That's when they can be resumed. This is done to avoid resuming processes before they start
// waiting.

class VlTriggerScheduler final {
    // TYPES
    using VlCoroutineVec = std::vector<VlCoroutineHandle>;

    // MEMBERS
    VlCoroutineVec m_awaiting;  // Coroutines suspended before ready() was called
                                // (not resumable)
    VlCoroutineVec m_fired;  // Coroutines that were triggered (all coros from m_awaiting are moved
                             // here in ready())
    VlCoroutineVec m_toResume;  // Coroutines to resume in next resumePrep()
                                // - moved here in commit()

public:
    // METHODS
    // Resumes all coroutines from the m_toResume
    void resume(const char* eventDescription = VL_UNKNOWN);
    // Moves all coroutines from m_fired to m_toResume
    void moveToResumeQueue(const char* eventDescription = VL_UNKNOWN);
    // Moves all coroutines from m_awaiting to m_fired
    void ready(const char* eventDescription = VL_UNKNOWN);
    // Are there no coroutines awaiting?
    bool empty() const { return m_fired.empty() && m_awaiting.empty(); }
#ifdef VL_DEBUG
    void dump(const char* eventDescription) const;
#endif
    // Used by coroutines for co_awaiting a certain trigger
    auto trigger(bool ready, const VlProcessRef& process,
                 const char* eventDescription = VL_UNKNOWN, const char* filename = VL_UNKNOWN,
                 int lineno = 0) {
        VL_DEBUG_IF(VL_DBG_MSGF("         Suspending process waiting for %s at %s:%d\n",
                                eventDescription, filename, lineno););
        struct Awaitable final {
            VlCoroutineVec& suspended;  // Coros waiting on trigger
            VlProcess* processp;  // Non-owning; null if process state unused
            VlFileLineDebug fileline;

            bool await_ready() const { return false; }  // Always suspend
            void await_suspend(std::coroutine_handle<VlPromise> coro) {
                suspended.emplace_back(coro, processp, fileline);
            }
            void await_resume() const {}
        };
        return Awaitable{ready ? m_fired : m_awaiting, process.get(),
                         VlFileLineDebug{filename, lineno}};
    }
};

//=============================================================================
// VlDynamicTriggerScheduler is used for cases where triggers cannot be statically referenced and
// evaluated. Coroutines that make use of this scheduler must adhere to a certain procedure:
//     __Vtrigger = 0;
//     <locals and inits required for trigger eval>
//     while (!__Vtrigger) {
//         co_await __VdynSched.evaluation();
//         <pre updates>;
//         __Vtrigger = <trigger eval>;
//         __VdynShed.anyTriggered(__Vtrigger);
//         [optionally] co_await __VdynSched.postUpdate();
//         <post updates>;
//     }
//    co_await __VdynSched.resumption();
// The coroutines get resumed at trigger evaluation time, evaluate their local triggers, optionally
// await the post update step, and if the trigger is set, await proper resumption in the 'act' eval
// step.

class VlDynamicTriggerScheduler final {
    // TYPES
    using VlCoroutineVec = std::vector<VlCoroutineHandle>;

    // MEMBERS
    bool m_anyTriggered = false;  // If true, at least one trigger was set
    VlCoroutineVec m_suspended;  // Suspended coroutines awaiting trigger evaluation
    VlCoroutineVec m_evaluated;  // Coroutines currently being evaluated (for evaluate())
    VlCoroutineVec m_triggered;  // Coroutines whose triggers were set, and are awaiting resumption
    VlCoroutineVec m_post;  // Coroutines awaiting the post update step (only relevant for triggers
                            // with destructive post updates, e.g. named events)

    // METHODS
    auto awaitable(const VlProcessRef& process, VlCoroutineVec& queue, const char* filename,
                   int lineno) {
        struct Awaitable final {
            VlProcess* processp;  // Non-owning; null if process state unused
            VlCoroutineVec& suspended;  // Coros waiting on trigger
            VlFileLineDebug fileline;

            bool await_ready() const { return false; }  // Always suspend
            void await_suspend(std::coroutine_handle<VlPromise> coro) {
                suspended.emplace_back(coro, processp, fileline);
            }
            void await_resume() const {}
        };
        return Awaitable{process.get(), queue, VlFileLineDebug{filename, lineno}};
    }

public:
    // Evaluates all dynamic triggers (resumed coroutines that co_await evaluation())
    bool evaluate();
    // Called by coroutines that evaluate triggers to notify the scheduler if any triggers were set
    void anyTriggered(bool triggered) { m_anyTriggered = m_anyTriggered || triggered; }
    // Runs post updates for all dynamic triggers (resumes coroutines that co_await postUpdate())
    void doPostUpdates();
    // Resumes all coroutines whose triggers are set (those that co_await resumption())
    void resume();
#ifdef VL_DEBUG
    void dump() const;
#endif
    // Used by coroutines for co_awaiting trigger evaluation
    auto evaluation(const VlProcessRef& process, const char* eventDescription,
                    const char* filename, int lineno) {
        VL_DEBUG_IF(VL_DBG_MSGF("         Suspending process waiting for %s at %s:%d\n",
                                eventDescription, filename, lineno););
        return awaitable(process, m_suspended, filename, lineno);
    }
    // Used by coroutines for co_awaiting the trigger post update step
    auto postUpdate(const VlProcessRef& process, const char* eventDescription,
                    const char* filename, int lineno) {
        VL_DEBUG_IF(
            VL_DBG_MSGF("         Process waiting for %s at %s:%d awaiting the post update step\n",
                        eventDescription, filename, lineno););
        return awaitable(process, m_post, filename, lineno);
    }
    // Used by coroutines for co_awaiting the resumption step (in 'act' eval)
    auto resumption(const VlProcessRef& process, const char* eventDescription,
                    const char* filename, int lineno) {
        VL_DEBUG_IF(VL_DBG_MSGF("         Process waiting for %s at %s:%d awaiting resumption\n",
                                eventDescription, filename, lineno););
        return awaitable(process, m_triggered, filename, lineno);
    }
};

//=============================================================================
// VlForkSync is used to manage fork..join and fork..join_any constructs.

// Shared fork..join state, because VlForkSync is copied into generated coroutine frames.
class VlForkSyncState final {
public:
    size_t m_counter = 0;  // When reaches 0, resume suspended coroutine
    VlCoroutineHandle m_susp;  // Coroutine to resume
    bool m_inited = false;  // Initialization complete
    size_t m_pendingDones = 0;  // done() calls seen before init() (e.g. early killed branch)
    bool m_inDone = false;  // Guard against re-entrant resume recursion from nested kills
    bool m_resumePending = false;  // Join reached zero again while inside done()

    VlForkSyncState()  // Construct with a null coroutine handle
        : m_susp{nullptr} {}
    void done(const char* filename = VL_UNKNOWN, int lineno = 0);
};

class VlForkSync final {
    // State shared between copies of this object
    std::shared_ptr<VlForkSyncState> m_state{std::make_shared<VlForkSyncState>()};

public:
    // Create the join object and set the counter to the specified number
    void init(size_t count, const VlProcessRef& process) {
        const size_t pendingDones = m_state->m_pendingDones;
        m_state->m_pendingDones = 0;
        count = (pendingDones >= count) ? 0 : (count - pendingDones);
        m_state->m_counter = count;
        m_state->m_susp = {process.get()};
        m_state->m_inited = true;
    }
    // Register process kill callback so killed fork branches still decrement join counter
    void onKill(VlProcessRef process);
    // Called whenever any of the forked processes finishes. If the join counter reaches 0, the
    // main process gets resumed
    void done(const char* filename = VL_UNKNOWN, int lineno = 0) {
        m_state->done(filename, lineno);
    }
    // Used by coroutines for co_awaiting a join
    auto join(const VlProcessRef& process, const char* filename = VL_UNKNOWN, int lineno = 0) {
        VL_DEBUG_IF(
            VL_DBG_MSGF("             Awaiting join of fork at: %s:%d\n", filename, lineno););
        struct Awaitable final {
            VlProcess* processp;  // Non-owning; null if process state unused
            const std::shared_ptr<VlForkSyncState> state;  // Join to await on
            VlFileLineDebug fileline;

            bool await_ready() { return state->m_counter == 0; }  // Suspend if join still exists
            void await_suspend(std::coroutine_handle<VlPromise> coro) {
                state->m_susp = {coro, processp, fileline};
            }
            void await_resume() const {}
        };
        return Awaitable{process.get(), m_state, VlFileLineDebug{filename, lineno}};
    }
};

//=============================================================================
// VlCoroutine
// Return value of a coroutine. Used for chaining coroutine suspension/resumption.

class VlCoroutine final {
public:
    // MEMBERS
    VlPromise* m_promisep;  // The promise created for this coroutine

    // TYPES
    using promise_type = VlPromise;  // promise_type has to be public

    // CONSTRUCTORS
    // Construct
    // cppcheck-suppress noExplicitConstructor
    VlCoroutine(VlPromise* promisep)
        : m_promisep{promisep} {
        m_promisep->m_corop = this;
    }
    // Move. Update the pointers each time the return object is moved
    // cppcheck-suppress noExplicitConstructor
    VlCoroutine(VlCoroutine&& other)
        : m_promisep{std::exchange(other.m_promisep, nullptr)} {
        if (m_promisep) m_promisep->m_corop = this;
    }
    ~VlCoroutine() {
        // Indicate to the promise that the return object is gone
        if (m_promisep) m_promisep->m_corop = nullptr;
    }

    // METHODS
    // Suspend the awaiter if the coroutine is suspended (the promise exists)
    bool await_ready() const noexcept { return !m_promisep; }
    // Set the awaiting coroutine as the continuation of the current coroutine
    // If the current coroutine is suspended forever, propagate that to the awaiting coroutine
    // In that case, m_continuation will be used for cleaning up the whole suspended coroutine
    // stack
    void await_suspend(std::coroutine_handle<VlPromise> awaiting_coro) {
        if (m_promisep->m_forever) awaiting_coro.promise().m_forever = true;
        m_promisep->m_continuation = awaiting_coro;
    }
    void await_resume() const noexcept {}
};

#endif  // Guard
