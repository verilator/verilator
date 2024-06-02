// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);

   event a, b, c;
   bit   wif[10], welse[10];
   bit   nif[10], nelse[10];

   initial begin
      wait_order (a, b) wif[0] = '1;
   end
`ifdef FAIL_ASSERT_1
   initial begin
      wait_order (b, a) nif[0] = '1;
   end
`endif

   initial begin
      wait_order (a, b) else welse[1] = '1;
   end
   initial begin
      wait_order (b, a) else nelse[1] = '1;
   end

   initial begin
      wait_order (a, b) wif[2] = '1; else welse[2] = '1;
   end
   initial begin
      wait_order (b, a) nif[2] = '1; else nelse[2] = '1;
   end

   initial begin
      #10;
      -> a;
      #10;
      -> b;
      #10;
      -> c;
      #10;

      `checkd(wif[0], 1'b1);
      `checkd(nif[0], 1'b0);

      `checkd(welse[1], 1'b0);
      `checkd(nelse[1], 1'b1);

      `checkd(wif[2], 1'b1);
      `checkd(welse[2], 1'b0);
      `checkd(nif[2], 1'b0);
      `checkd(nelse[2], 1'b1);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
