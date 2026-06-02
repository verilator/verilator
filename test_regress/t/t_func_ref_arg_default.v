// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A task argument that defaults to a plain variable must alias that variable,
// not a copy of it: a write through a 'ref' default must propagate back, and a
// 'const ref' default must observe later updates to the variable.

module t;
   logic clk = 0;
   initial forever #5 clk = ~clk;

   int   shared = 5;
   logic flag = 0;
   logic done = 0;

   // writable 'ref' default: a write through it must reach 'shared'
   task automatic incr(ref int r = shared);
      r = r + 10;
   endtask

   // 'const ref' default: must observe a later update to 'flag'
   task automatic waitflag(const ref logic r = flag);
      @(posedge clk);
      while (!r) @(posedge clk);
      done <= 1'b1;
   endtask

   initial begin
      incr();
      if (shared !== 15) begin
         $write("%%Error: write through default 'ref' lost (shared=%0d)\n", shared);
         $stop;
      end
      fork waitflag(); join_none
      repeat (3) @(posedge clk);
      flag = 1'b1;
      repeat (5) @(posedge clk);
      if (done !== 1'b1) begin
         $write("%%Error: default 'const ref' did not observe update\n");
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
