// DESCRIPTION: Verilator: built-in packages and classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2022-2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated IEEE std:: header
///
/// This file is included automatically by Verilator when a std::mailbox or
/// std::semaphore is referenced.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
//*************************************************************************

// verilator lint_off DECLFILENAME
// verilator lint_off TIMESCALEMOD
// verilator lint_off UNUSEDSIGNAL
package std;
    // The process class is not implemented, but it's predeclared here,
    // so the linter accepts references to it.
    typedef class process;

    class mailbox #(type T);
        protected int m_bound;
        protected T m_queue[$];

        function new(int bound = 0);
            m_bound = bound;
        endfunction

        function int num();
            return m_queue.size();
        endfunction

        task put(T message);
    `ifdef VERILATOR_TIMING
            if (m_bound != 0)
                wait (m_queue.size() < m_bound);
            m_queue.push_back(message);
    `endif
        endtask

        function int try_put(T message);
            if (num() < m_bound) begin
                m_queue.push_back(message);
                return 1;
            end
            return 0;
        endfunction

        task get(ref T message);
    `ifdef VERILATOR_TIMING
            wait (m_queue.size() > 0);
            message = m_queue.pop_front();
    `endif
        endtask

        function int try_get(ref T message);
            if (num() > 0) begin
                message = m_queue.pop_front();
                return 1;
            end
            return 0;
        endfunction

        task peek(ref T message);
    `ifdef VERILATOR_TIMING
            wait (m_queue.size() > 0);
            message = m_queue[0];
    `endif
        endtask

        function int try_peek(ref T message);
            if (num() > 0) begin
                message = m_queue[0];
                return 1;
            end
            return 0;
        endfunction
    endclass

    class semaphore;
        protected int m_keyCount;

        function new(int keyCount = 0);
            m_keyCount = keyCount;
        endfunction

        function void put(int keyCount = 1);
            m_keyCount += keyCount;
        endfunction

        task get(int keyCount = 1);
    `ifdef VERILATOR_TIMING
            wait (m_keyCount >= keyCount);
            m_keyCount -= keyCount;
    `endif
        endtask

        function int try_get(int keyCount = 1);
            if (m_keyCount >= keyCount) begin
                m_keyCount -= keyCount;
                return 1;
            end
            return 0;
        endfunction
    endclass
endpackage
