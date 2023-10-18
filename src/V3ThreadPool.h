// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Thread pool for Verilator itself
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2023 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3THREADPOOL_H_
#define _V3THREADPOOL_H_ 1

#ifdef VL_MT_DISABLED_CODE_UNIT
#error "Source file has been declared as MT_DISABLED, threads use is prohibited."
#endif

#include "V3Mutex.h"
#include "V3ThreadSafety.h"

#include <condition_variable>
#include <functional>
#include <future>
#include <list>
#include <mutex>
#include <queue>
#include <thread>

//============================================================================

// Callable, type-erased wrapper for std::packaged_task<Signature> with any Signature.
class VAnyPackagedTask final {
    // TYPES
    struct PTWrapperBase {
        virtual ~PTWrapperBase() {}
        virtual void operator()() = 0;
    };

    template <typename Signature>
    struct PTWrapper final : PTWrapperBase {
        std::packaged_task<Signature> m_pt;

        explicit PTWrapper(std::packaged_task<Signature>&& pt)
            : m_pt(std::move(pt)) {}

        void operator()() final override { m_pt(); }
    };

    // MEMBERS
    std::unique_ptr<PTWrapperBase> m_ptWrapperp = nullptr;  // Wrapper to call

public:
    // CONSTRUCTORS
    template <typename Signature>
    // non-explicit:
    // cppcheck-suppress noExplicitConstructor
    VAnyPackagedTask(std::packaged_task<Signature>&& pt)
        : m_ptWrapperp{std::make_unique<PTWrapper<Signature>>(std::move(pt))} {}

    VAnyPackagedTask() = default;
    ~VAnyPackagedTask() = default;

    VAnyPackagedTask(const VAnyPackagedTask&) = delete;
    VAnyPackagedTask& operator=(const VAnyPackagedTask&) = delete;

    VAnyPackagedTask(VAnyPackagedTask&&) = default;
    VAnyPackagedTask& operator=(VAnyPackagedTask&&) = default;

    // METHODS
    // Call the wrapped function
    void operator()() { (*m_ptWrapperp)(); }
};

class V3ThreadPool final {
    // MEMBERS
    static constexpr unsigned int FUTUREWAITFOR_MS = 100;

    // some functions locks both of this mutexes, be careful of lock inversion problems
    // 'm_stoppedJobsMutex' mutex should always be locked before 'm_mutex' mutex
    // check usage of both of them when you use either of them
    V3Mutex m_mutex;  // Mutex for use by m_queue
    V3Mutex m_stoppedJobsMutex;  // Used to signal stopped jobs
    std::queue<VAnyPackagedTask> m_queue VL_GUARDED_BY(m_mutex);  // Queue of jobs
    // We don't need to guard this condition_variable as
    // both `notify_one` and `notify_all` functions are atomic,
    // `wait` function is not atomic, but we are guarding `m_queue` that is
    // used by this condition_variable, so clang checks that we have mutex locked
    std::condition_variable_any m_cv;  // Conditions to wake up workers
    std::list<std::thread> m_workers;  // Worker threads
    // Number of started and not yet finished jobs.
    // Reading is valid only after call to `stopOtherThreads()` or when no worker threads exist.
    std::atomic_uint m_jobsInProgress{0};
    // Conditions to wake up stopped jobs
    std::condition_variable_any m_stoppedJobsCV VL_GUARDED_BY(m_stoppedJobsMutex);
    // Conditions to wake up exclusive access thread
    std::condition_variable_any m_exclusiveAccessThreadCV VL_GUARDED_BY(m_stoppedJobsMutex);
    std::atomic_uint m_stoppedJobs{0};  // Currently stopped jobs waiting for wake up
    std::atomic_bool m_stopRequested{false};  // Signals to resume stopped jobs
    std::atomic_bool m_exclusiveAccess{false};  // Signals that all other threads are stopped

    std::atomic_bool m_shutdown{false};  // Termination pending

    // Indicates whether multithreading has been suspended.
    // Used for error detection in resumeMultithreading only. You probably should use
    // m_exclusiveAccess for information whether something should be run in current thread.
    bool m_multithreadingSuspended VL_GUARDED_BY(m_mutex) = false;

    // CONSTRUCTORS
    V3ThreadPool() = default;
    ~V3ThreadPool() {
        if (!m_mutex.try_lock()) {
            if (m_jobsInProgress != 0) {
                // ThreadPool shouldn't be destroyed when jobs are running and mutex is locked,
                // something is wrong. Most likely Verilator is exitting as a result of failed
                // assert in critical section. Do nothing, let it exit.
                return;
            }
        } else {
            V3LockGuard lock{m_mutex, std::adopt_lock_t{}};
            m_queue = {};  // make sure queue is empty
        }
        resize(0);
    }

public:
    // Request exclusive access to processing for the object lifetime.
    class ScopedExclusiveAccess;

    // METHODS
    // Singleton
    static V3ThreadPool& s() VL_MT_SAFE {
        static V3ThreadPool s_s;
        return s_s;
    }

    // Resize thread pool to n workers (queue must be empty)
    void resize(unsigned n) VL_MT_UNSAFE VL_EXCLUDES(m_mutex) VL_EXCLUDES(m_stoppedJobsMutex)
        VL_EXCLUDES(V3MtDisabledLock::instance());

    // Enqueue a job for asynchronous execution
    // Due to missing support for lambda annotations in c++11,
    // `clang_check_attributes` script assumes that if
    // function takes `std::function` as argument, it
    // will call it. `VL_MT_START` here indicates that
    // every function call inside this `std::function` requires
    // annotations.
    template <typename Callable>
    auto enqueue(Callable&& f) VL_MT_START;

    // Request exclusive access to processing.
    // It sends request to stop all other threads and waits for them to stop.
    // Other threads needs to manually call 'check_stop_requested' in places where
    // they can be stopped.
    // When all other threads are stopped, this function executes the job
    // and resumes execution of other jobs.
    template <typename Callable>
    void requestExclusiveAccess(Callable&& exclusiveAccessJob) VL_MT_SAFE
        VL_EXCLUDES(m_stoppedJobsMutex);

    // Check if other thread requested exclusive access to processing,
    // if so, it waits for it to complete. Afterwards it is resumed.
    // Returns true if request was send and we waited, otherwise false
    bool waitIfStopRequested() VL_MT_SAFE VL_EXCLUDES(m_stoppedJobsMutex);

    // Waits for future.
    // This function can be interupted by exclusive access request.
    // When other thread requested exclusive access to processing,
    // current thread is stopped and waits until it is resumed.
    // Returns future result
    template <typename T>
    static T waitForFuture(std::future<T>& future) VL_MT_SAFE_EXCLUDES(m_mutex);

    // Waits for list of futures
    // This function can be interupted by exclusive access request.
    // When other thread requested exclusive access to processing,
    // current thread is stopped and waits until it is resumed.
    // This function uses function overload instead of template
    // specialization as C++11 requires them to be inside namespace scope
    // Returns list of future result or void
    template <typename T>
    static auto waitForFutures(std::list<std::future<T>>& futures) {
        return waitForFuturesImp(futures);
    }

    static void selfTest();
    static void selfTestMtDisabled() VL_MT_DISABLED;

private:
    // For access to suspendMultithreading() and resumeMultithreading()
    friend class V3MtDisabledLock;

    // Temporarily suspends multithreading.
    //
    // Existing worker threads are not terminated. All jobs enqueued when multithreading is
    // suspended are executed synchronously.
    // Must be called from the main thread. Jobs queue must be empty. Existing worker threads must
    // be idle.
    //
    // Only V3MtDisabledLock class is supposed to use this function.
    void suspendMultithreading() VL_MT_SAFE VL_EXCLUDES(m_mutex) VL_EXCLUDES(m_stoppedJobsMutex);

    // Resumes multithreading suspended previously by call tosuspendMultithreading().
    //
    // Only V3MtDisabledLock class is supposed to use this function.
    void resumeMultithreading() VL_MT_SAFE VL_EXCLUDES(m_mutex) VL_EXCLUDES(m_stoppedJobsMutex);

    template <typename T>
    static std::list<T> waitForFuturesImp(std::list<std::future<T>>& futures) {
        std::list<T> results;
        while (!futures.empty()) {
            results.push_back(V3ThreadPool::waitForFuture(futures.front()));
            futures.pop_front();
        }
        return results;
    }

    static void waitForFuturesImp(std::list<std::future<void>>& futures) {
        while (!futures.empty()) {
            V3ThreadPool::waitForFuture(futures.front());
            futures.pop_front();
        }
    }
    bool willExecuteSynchronously() const VL_MT_SAFE {
        return m_workers.empty() || m_exclusiveAccess;
    }

    // True when any thread requested exclusive access
    bool stopRequested() const VL_MT_SAFE {
        // don't wait if shutdown already requested
        if (m_shutdown) return false;
        return m_stopRequested;
    }

    // Waits until `resumeOtherThreads()` is called or exclusive access scope end.
    void waitForResumeRequest() VL_REQUIRES(m_stoppedJobsMutex);

    // Sends stop request to other threads and waits until they stop.
    void stopOtherThreads() VL_MT_SAFE_EXCLUDES(m_mutex) VL_REQUIRES(m_stoppedJobsMutex);

    // Resumes threads stopped through previous call to `stopOtherThreads()`.
    void resumeOtherThreads() VL_MT_SAFE_EXCLUDES(m_mutex) VL_REQUIRES(m_stoppedJobsMutex) {
        m_stopRequested = false;
        m_stoppedJobsCV.notify_all();
    }

    void workerJobLoop(int id) VL_MT_SAFE;

    static void startWorker(V3ThreadPool* selfThreadp, int id) VL_MT_SAFE;
};

class VL_SCOPED_CAPABILITY V3ThreadPool::ScopedExclusiveAccess final {
public:
    ScopedExclusiveAccess() VL_ACQUIRE(V3ThreadPool::s().m_stoppedJobsMutex) VL_MT_SAFE {
        if (!V3ThreadPool::s().willExecuteSynchronously()) {
            V3ThreadPool::s().m_stoppedJobsMutex.lock();

            if (V3ThreadPool::s().stopRequested()) { V3ThreadPool::s().waitForResumeRequest(); }
            V3ThreadPool::s().stopOtherThreads();
            V3ThreadPool::s().m_exclusiveAccess = true;
        } else {
            V3ThreadPool::s().m_stoppedJobsMutex.assumeLocked();
        }
    }
    ~ScopedExclusiveAccess() VL_RELEASE(V3ThreadPool::s().m_stoppedJobsMutex) VL_MT_SAFE {
        // Can't use `willExecuteSynchronously`, we're still in exclusive execution state.
        if (V3ThreadPool::s().m_exclusiveAccess) {
            V3ThreadPool::s().m_exclusiveAccess = false;
            V3ThreadPool::s().resumeOtherThreads();

            V3ThreadPool::s().m_stoppedJobsMutex.unlock();
            // wait for all threads to resume
            while (V3ThreadPool::s().m_stoppedJobs != 0) {}
        } else {
            V3ThreadPool::s().m_stoppedJobsMutex.pretendUnlock();
        }
    }
};

template <typename T>
T V3ThreadPool::waitForFuture(std::future<T>& future) VL_MT_SAFE_EXCLUDES(m_mutex) {
    while (true) {
        V3ThreadPool::s().waitIfStopRequested();
        {
            std::future_status status
                = future.wait_for(std::chrono::milliseconds(V3ThreadPool::FUTUREWAITFOR_MS));
            switch (status) {
            case std::future_status::deferred: continue;
            case std::future_status::timeout: continue;
            case std::future_status::ready: return future.get();
            }
        }
    }
}

template <typename Callable>
auto V3ThreadPool::enqueue(Callable&& f) VL_MT_START {
    using result_t = decltype(f());
    auto&& job = std::packaged_task<result_t()>{std::forward<Callable>(f)};
    auto future = job.get_future();
    if (willExecuteSynchronously()) {
        job();
    } else {
        {
            const V3LockGuard guard{m_mutex};
            m_queue.push(std::move(job));
        }
        m_cv.notify_one();
    }
    return future;
}

template <typename Callable>
void V3ThreadPool::requestExclusiveAccess(Callable&& exclusiveAccessJob) VL_MT_SAFE
    VL_EXCLUDES(m_stoppedJobsMutex) {
    ScopedExclusiveAccess exclusive_access;
    exclusiveAccessJob();
}

#endif  // Guard
