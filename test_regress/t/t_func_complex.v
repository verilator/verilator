// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();
   typedef integer q_t[$];

   function void queue_set(ref q_t q);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      q.push_back(42);
   endfunction

   function void queue_check_nref(q_t q);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      q[0] = 11;
      if (q[0] != 11) $stop;
   endfunction

   function void queue_check_ref(const ref q_t q);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      if (q[0] != 42) $stop;
   endfunction

   function q_t queue_ret();
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      queue_ret = '{101};
   endfunction

   initial begin
      q_t iq;
      queue_set(iq);
      queue_check_ref(iq);

      iq[0] = 44;
      queue_check_nref(iq);
      if (iq[0] != 44) $stop;

      iq = queue_ret();
      if (iq[0] != 101) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
