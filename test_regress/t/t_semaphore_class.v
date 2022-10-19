// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class semaphore_cls;
   // Test an implementation similar to what Verilator will do internally
   int m_keys;
   function new(int keyCount = 0);
      m_keys = keyCount;
   endfunction
   function void put(int keyCount = 1);
      m_keys += keyCount;
   endfunction
   task get(int keyCount = 1);
      wait (m_keys >= keyCount);
      m_keys -= keyCount;
   endtask
   function int try_get(int keyCount = 1);
      if (m_keys >= keyCount) begin
         m_keys -= keyCount;
         return 1;
      end
      else begin
         return 0;
      end
   endfunction
endclass

`define SEMAPHORE_T semaphore_cls

`include "t_semaphore.v"
