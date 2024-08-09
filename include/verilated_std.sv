// DESCRIPTION: Verilator: built-in packages and classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2022-2024 by Wilson Snyder. This program is free software; you can
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
         while (m_bound != 0 && m_queue.size() >= m_bound)
            wait (m_queue.size() < m_bound);
         m_queue.push_back(message);
`endif
      endtask

      function int try_put(T message);
         if (m_bound == 0 || num() < m_bound) begin
            m_queue.push_back(message);
            return 1;
         end
         return 0;
      endfunction

      task get(ref T message);
`ifdef VERILATOR_TIMING
         while (m_queue.size() == 0) begin
            wait (m_queue.size() > 0);
         end
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
         while (m_queue.size() == 0) begin
            wait (m_queue.size() > 0);
         end
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
         while (m_keyCount < keyCount) begin
            wait (m_keyCount >= keyCount);
         end
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

   class process;
      typedef enum {
         FINISHED  = 0,
         RUNNING   = 1,
         WAITING   = 2,
         SUSPENDED = 3,
         KILLED    = 4
      } state;

`ifdef VERILATOR_TIMING
      // Width visitor changes it to VlProcessRef
      protected chandle m_process;
`endif

      static function process self();
         process p = new;
`ifdef VERILATOR_TIMING
         $c(p.m_process, " = vlProcess;");
`endif
         return p;
      endfunction

      protected function void set_status(state s);
`ifdef VERILATOR_TIMING
         $c(m_process, "->state(", s, ");");
`endif
      endfunction

      function state status();
`ifdef VERILATOR_TIMING
         return state'($c(m_process, "->state()"));
`else
         return RUNNING;
`endif
      endfunction

      function void kill();
         set_status(KILLED);
      endfunction

      function void suspend();
         $error("std::process::suspend() not supported");
      endfunction

      function void resume();
         set_status(RUNNING);
      endfunction

      task await();
`ifdef VERILATOR_TIMING
         wait (status() == FINISHED || status() == KILLED);
`endif
      endtask

      // When really implemented, srandom must operate on the process, but for
      // now rely on the srandom() that is automatically generated for all
      // classes.
      //
      // function void srandom(int seed);
      // endfunction

      // The methods below work only if set_randstate is never applied to
      // a state string created before another such string. Full support
      // could use VlRNG class to store the state per process in VlProcess
      // objects.
      function string get_randstate();
         string s;

         s.itoa($random);  // Get a random number
         set_randstate(s);  // Pretend it's the state of RNG
         return s;
      endfunction

      function void set_randstate(string s);
         $urandom(s.atoi());  // Set the seed using a string
      endfunction
   endclass
   function int randomize();
      randomize = 0;
   endfunction
endpackage
