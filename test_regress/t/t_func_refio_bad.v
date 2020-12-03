// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();
   typedef integer q_t[$];

   function void queue_set(ref q_t q);
      q.push_back(42);
   endfunction

   initial begin
      q_t iq;
      queue_set(42);  // 42 is bad, meant iq
   end
endmodule
