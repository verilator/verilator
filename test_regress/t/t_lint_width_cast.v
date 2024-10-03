// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);

   wire [5:0] b1 = 6'b101101;
   wire [5:0] b2 = 6'b011110;
   logic [5:0] a6;
   logic [9:0] a10;

   initial begin
      // issue #3417
      a6 = b2 - b1;
      `checkh(a6, 6'h31);
      a10 = 10'(b2 - b1);
      `checkh(a10, 10'h3f1);  // This being not 31 indicates operator expands
      `checkh($bits(10'(b1)), 10);
      `checkh($bits(10'(b2 - b1)), 10);
      `checkh($bits(b2 - b1), 6);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
