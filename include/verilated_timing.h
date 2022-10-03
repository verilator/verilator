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

// clang-format off
// Some preprocessor magic to support both Clang and GCC coroutines with both libc++ and libstdc++
#ifdef __clang__
# if __clang_major__ < 14
#  ifdef __GLIBCXX__ // Using stdlibc++
#   define __cpp_impl_coroutine 1  // Clang doesn't define this, but it's needed for libstdc++
#   include <coroutine>
    namespace std { // Bring coroutine library into std::experimental, as Clang < 14 expects it to be there
        namespace experimental {
            using namespace std;
        }
    }
#  else // Using libc++
#   include <experimental/coroutine> // Clang older than 14, coroutines are under experimental
    namespace std {
        using namespace experimental; // Bring std::experimental into the std namespace
    }
#  endif
# else // Clang >= 14
#  if __GLIBCXX__ // Using stdlibc++
#   define __cpp_impl_coroutine 1  // Clang doesn't define this, but it's needed for libstdc++
#  endif
#  include <coroutine>
# endif
#else  // Not Clang
# include <coroutine>
#endif
// clang-format on

//=============================================================================
// VlCoroutineHandle is a non-copyable (but movable) coroutine handle. On resume, the handle is
// cleared, as we assume that either the coroutine has finished and deleted itself, or, if it got
// suspended, another VlCoroutineHandle was created to manage it.

class VlCoroutineHandle final {
    VL_UNCOPYABLE(VlCoroutineHandle);

    // MEMBERS
    std::coroutine_handle<> m_coro;  // The wrapped coroutine handle
#ifdef VL_DEBUG
    const char* m_filename;
    int m_linenum;
#endif

public:
    // CONSTRUCTORS
    // Construct
    VlCoroutineHandle(std::coroutine_handle<> coro = nullptr, const char* filename = nullptr,
                      int linenum = 0)
        : m_coro{coro}
#ifdef VL_DEBUG
        , m_filename{filename}
        , m_linenum{linenum}
#endif
    {
    }
    // Move the handle, leaving a nullptr
    VlCoroutineHandle(VlCoroutineHandle&& moved)
        : m_coro{std::exchange(moved.m_coro, nullptr)}
#ifdef VL_DEBUG
        , m_filename{moved.m_filename}
        , m_linenum{moved.m_linenum}
#endif
    {
    }
    // Destroy if the handle isn't null
    ~VlCoroutineHandle() {
        // Usually these coroutines should get resumed; we only need to clean up if we destroy a
        // model with some coroutines suspended
        if (VL_UNLIKELY(m_coro)) m_coro.destroy();
    }
    // METHODS
    // Move the handle, leaving a null handle
    auto& operator=(VlCoroutineHandle&& moved) {
        m_coro = std::exchange(moved.m_coro, nullptr);
        return *this;
    }
    // Resume the coroutine if the handle isn't null
    void resume();
#ifdef VL_DEBUG
    void dump();
#endif
};

//=============================================================================
// VlDelayScheduler stores coroutines to be resumed at a certain simulation time. If the current
// time is equal to a coroutine's resume time, the coroutine gets resumed.

class VlDelayScheduler final {
    // TYPES
    struct VlDelayedCoroutine {
        uint64_t m_timestep;  // Simulation time when the coroutine should be resumed
        VlCoroutineHandle m_handle;  // The suspended coroutine to be resumed

        // Comparison operator for std::push_heap(), std::pop_heap()
        bool operator<(const VlDelayedCoroutine& other) const {
            return m_timestep > other.m_timestep;
        }
#ifdef VL_DEBUG
        void dump();
#endif
    };
    using VlDelayedCoroutineQueue = std::vector<VlDelayedCoroutine>;

    // MEMBERS
    VerilatedContext& m_context;
    VlDelayedCoroutineQueue m_queue;  // Coroutines to be restored at a certain simulation time

public:
    // CONSTRUCTORS
    explicit VlDelayScheduler(VerilatedContext& context)
        : m_context{context} {}
    // METHODS
    // Resume coroutines waiting for the current simulation time
    void resume();
    // Returns the simulation time of the next time slot (aborts if there are no delayed
    // coroutines)
    uint64_t nextTimeSlot();
    // Are there no delayed coroutines awaiting?
    bool empty() { return m_queue.empty(); }
    // Are there coroutines to resume at the current simulation time?
    bool awaitingCurrentTime() {
        return !empty() && m_queue.front().m_timestep <= m_context.time();
    }
#ifdef VL_DEBUG
    void dump();
#endif
    // Used by coroutines for co_awaiting a certain simulation time
    auto delay(uint64_t delay, const char* filename, int linenum) {
        struct Awaitable {
            VlDelayedCoroutineQueue& queue;
            uint64_t delay;
#ifdef VL_DEBUG
            const char* filename;
            int linenum;
#endif
            bool await_ready() { return false; }  // Always suspend
            void await_suspend(std::coroutine_handle<> coro) {
#ifdef VL_DEBUG
                queue.push_back({delay, VlCoroutineHandle{coro, filename, linenum}});
#else
                queue.push_back({delay, coro});
#endif
                // Move last element to the proper place in the max-heap
                std::push_heap(queue.begin(), queue.end());
            }
            void await_resume() {}
        };
#ifdef VL_DEBUG
        return Awaitable{m_queue, m_context.time() + delay, filename, linenum};
#else
        return Awaitable{m_queue, m_context.time() + delay};
#endif
    }
};

//=============================================================================
// VlTriggerScheduler stores coroutines to be resumed by a trigger. It does not keep track of its
// trigger, relying on calling code to resume when appropriate. Coroutines are kept in two stages
// - 'uncommitted' and 'ready'. Whenever a coroutine is suspended, it lands in the 'uncommited'
// stage. Only when commit() is called, these coroutines get moved to the 'ready' stage. That's
// when they can be resumed. This is done to avoid resuming processes before they start waiting.

class VlTriggerScheduler final {
    // TYPES
    using VlCoroutineVec = std::vector<VlCoroutineHandle>;

    // MEMBERS
    VlCoroutineVec m_uncommitted;  // Coroutines suspended before commit() was called
                                   // (not resumable)
    VlCoroutineVec m_ready;  // Coroutines that can be resumed (all coros from m_uncommitted are
                             // moved here in commit())

public:
    // METHODS
    // Resumes all coroutines from the 'ready' stage
    void resume(const char* eventDescription);
    // Moves all coroutines from m_uncommitted to m_ready
    void commit(const char* eventDescription);
    // Are there no coroutines awaiting?
    bool empty() { return m_ready.empty() && m_uncommitted.empty(); }
#ifdef VL_DEBUG
    void dump(const char* eventDescription);
#endif
    // Used by coroutines for co_awaiting a certain trigger
    auto trigger(const char* eventDescription, const char* filename, int linenum) {
        VL_DEBUG_IF(VL_DBG_MSGF("         Suspending process waiting for %s at %s:%d\n",
                                eventDescription, filename, linenum););
        struct Awaitable {
            VlCoroutineVec& suspended;  // Coros waiting on trigger
#ifdef VL_DEBUG
            const char* filename;
            int linenum;
#endif
            bool await_ready() { return false; }  // Always suspend
            void await_suspend(std::coroutine_handle<> coro) {
#ifdef VL_DEBUG
                suspended.emplace_back(coro, filename, linenum);
#else
                suspended.emplace_back(coro);
#endif
            }
            void await_resume() {}
        };
#ifdef VL_DEBUG
        return Awaitable{m_uncommitted, filename, linenum};
#else
        return Awaitable{m_uncommitted};
#endif
    }
};

//=============================================================================
// VlNow is a helper awaitable type that always suspends, and then immediately resumes a coroutine.
// Allows forcing the move of coroutine locals to the heap.

struct VlNow {
    bool await_ready() { return false; }  // Always suspend
    bool await_suspend(std::coroutine_handle<>) { return false; }  // Resume immediately
    void await_resume() {}
};

//=============================================================================
// VlForever is a helper awaitable type for suspending coroutines forever. Used for constant
// wait statements.

struct VlForever {
    bool await_ready() { return false; }  // Always suspend
    void await_suspend(std::coroutine_handle<> coro) { coro.destroy(); }
    void await_resume() {}
};

//=============================================================================
// VlForkSync is used to manage fork..join and fork..join_any constructs.

class VlForkSync final {
    // VlJoin stores the handle of a suspended coroutine that did a fork..join or fork..join_any.
    // If the counter reaches 0, the suspended coroutine shall be resumed.
    struct VlJoin {
        size_t m_counter = 0;  // When reaches 0, resume suspended coroutine
        VlCoroutineHandle m_susp;  // Coroutine to resume
    };

    // The join info is shared among all forked processes
    std::shared_ptr<VlJoin> m_join;

public:
    // Create the join object and set the counter to the specified number
    void init(size_t count) { m_join.reset(new VlJoin{count, {}}); }
    // Called whenever any of the forked processes finishes. If the join counter reaches 0, the
    // main process gets resumed
    void done(const char* filename, int linenum);
    // Used by coroutines for co_awaiting a join
    auto join(const char* filename, int linenum) {
        assert(m_join);
        VL_DEBUG_IF(
            VL_DBG_MSGF("             Awaiting join of fork at: %s:%d\n", filename, linenum););
        struct Awaitable {
            const std::shared_ptr<VlJoin> join;  // Join to await on
            bool await_ready() { return join->m_counter == 0; }  // Suspend if join still exists
            void await_suspend(std::coroutine_handle<> coro) { join->m_susp = coro; }
            void await_resume() {}
        };
        return Awaitable{m_join};
    }
};

//=============================================================================
// VlCoroutine
// Return value of a coroutine. Used for chaining coroutine suspension/resumption.

class VlCoroutine final {
private:
    // TYPES
    struct VlPromise {
        std::coroutine_handle<> m_continuation;  // Coroutine to resume after this one finishes
        VlCoroutine* m_corop = nullptr;  // Pointer to the coroutine return object

        ~VlPromise();

        VlCoroutine get_return_object() { return {this}; }

        // Never suspend at the start of the coroutine
        std::suspend_never initial_suspend() { return {}; }

        // Never suspend at the end of the coroutine (thanks to this, the coroutine will clean up
        // after itself)
        std::suspend_never final_suspend() noexcept;

        void unhandled_exception() { std::abort(); }
        void return_void() const {}
    };

    // MEMBERS
    VlPromise* m_promisep;  // The promise created for this coroutine

public:
    // TYPES
    using promise_type = VlPromise;  // promise_type has to be public

    // CONSTRUCTORS
    // Construct
    VlCoroutine(VlPromise* promisep)
        : m_promisep{promisep} {
        m_promisep->m_corop = this;
    }
    // Move. Update the pointers each time the return object is moved
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
    void await_suspend(std::coroutine_handle<> coro) { m_promisep->m_continuation = coro; }
    void await_resume() const noexcept {}
};

#endif  // Guard
