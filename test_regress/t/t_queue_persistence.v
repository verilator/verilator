// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);

   int q[$];

   task automatic func(ref int vrefed);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      `checkd(vrefed, 2);
      #100;
      vrefed = 10;
      `checkd(vrefed, 10);
   endtask

   initial begin
      q.push_back(1);
      q.push_back(2);
      q.push_back(3);
      `checkd(q[0], 1);
      `checkd(q[1], 2);
      `checkd(q[2], 3);
      func(q[1]);
   end

   initial begin
      #50;
      `checkd(q[1], 2);
      q.delete();
      #100;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
