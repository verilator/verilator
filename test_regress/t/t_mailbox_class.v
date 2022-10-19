// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class mailbox_cls #(type T=int);
   // Test an implementation similar to what Verilator will do internally
   int m_bound;
   T m_q[$];

   function new(int bound = 0);
      m_bound = bound;
   endfunction

   function int num();
      return m_q.size();
   endfunction

   task put(T message);
      if (m_bound != 0) wait (m_q.size() < m_bound);
      m_q.push_back(message);
   endtask
   function int try_put(T message);
      if (m_bound != 0 && m_q.size() < m_bound) begin
         m_q.push_back(message);
         return 1;
      end
      else begin
         return 0;
      end
   endfunction

   task get(ref T message);
      wait (m_q.size() != 0);
      message = m_q.pop_front();
   endtask
   function int try_get(ref T message);
      if (m_q.size() != 0) begin
         message = m_q.pop_front();
         return 1;
      end
      else begin
         return 0;
      end
   endfunction

   task peek(ref T message);
      wait (m_q.size() != 0);
      message = m_q[0];
   endtask
   function int try_peek(ref T message);
      if (m_q.size() != 0) begin
         message = m_q[0];
         return 1;
      end
      else begin
         return 0;
      end
   endfunction
endclass

`define MAILBOX_T mailbox_cls

`include "t_mailbox.v"
