// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class semaphore_cls;
   class InnerKeyClass;
      int innerKeys;
      function new(int keyCount = 0);
         innerKeys = keyCount;
      endfunction
   endclass
   // Test an implementation similar to what Verilator will do internally
   InnerKeyClass m_keys;
   function new(int keyCount = 0);
      m_keys = new(keyCount);
   endfunction
   function void put(int keyCount = 1);
      m_keys.innerKeys += keyCount;
   endfunction
   task get(int keyCount = 1);
      wait (m_keys.innerKeys >= keyCount);
      m_keys.innerKeys -= keyCount;
   endtask
   function int try_get(int keyCount = 1);
      if (m_keys.innerKeys >= keyCount) begin
         m_keys.innerKeys -= keyCount;
         return 1;
      end
      else begin
         return 0;
      end
   endfunction
endclass

`define SEMAPHORE_T semaphore_cls

`include "t_semaphore.v"
