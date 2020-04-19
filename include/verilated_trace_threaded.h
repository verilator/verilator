// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Threaded tracing internals
///
//=============================================================================
// SPDIFF_OFF

#ifndef _VERILATED_TRACE_THREADED_H_
#define _VERILATED_TRACE_THREADED_H_ 1

#include <deque>
#include <condition_variable>
#include <mutex>

// A simple synchronized first in first out queue
template <class T> class VerilatedThreadQueue {
private:
    std::deque<T> m_queue;
    std::condition_variable m_cv;
    std::mutex m_mutex;

public:
    // Put an element at the back of the queue
    void put(T value) {
        std::lock_guard<std::mutex> lockGuard(m_mutex);
        m_queue.push_back(value);
        m_cv.notify_one();
    }

    // Put an element at the front of the queue
    void put_front(T value) {
        std::lock_guard<std::mutex> lockGuard(m_mutex);
        m_queue.push_front(value);
        m_cv.notify_one();
    }

    // Get an element from the front of the queue. Blocks if none available
    T get() {
        std::unique_lock<std::mutex> lock(m_mutex);

        m_cv.wait(lock, [&] { return !m_queue.empty(); });

        assert(!m_queue.empty());

        T value = m_queue.front();
        m_queue.pop_front();

        return value;
    }

    // Non blocking get
    bool tryGet(T& result) {
        std::lock_guard<std::mutex> lockGuard(m_mutex);

        if (m_queue.empty()) { return false; }

        result = m_queue.front();
        m_queue.pop_front();

        return true;
    }
};

// Commands used by thread tracing. Note that the bottom 8 bits of all these
// values are empty and are used to store small amounts of additional command
// parameters.
typedef enum : vluint32_t {
    CHG_BIT = 0x0000,
    CHG_BUS = 0x0100,
    CHG_QUAD = 0x0200,
    CHG_ARRAY = 0x0300,
    CHG_FLOAT = 0x0400,
    CHG_DOUBLE = 0x0500,
    TIME_CHANGE = 0x8000,
    END = 0xf000,  // End of buffer
    SHUTDOWN = 0xf200  // Shutdown worker thread, also marks end of buffer
} VerilatedTraceCommand;

typedef union {
    vluint32_t cmd;  // Command code + params in bottom 8 bits
    vluint32_t* oldp;  // Pointer to previous value buffer to consult/update
    // Note: These are 64-bit wide, as this union already has a pointer type in it.
    vluint64_t params;  // Command parameter
    // New signal value in various forms
    vluint64_t newBits;
    float newFloat;
    double newDouble;
    vluint64_t timeui;
} VerilatedTraceEntry;

#endif  // guard
