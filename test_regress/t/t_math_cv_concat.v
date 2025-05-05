// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   // Issue #5972

   reg clk;
   reg signed [28:28] in1;
   reg signed [21:8] reg_10;

   // verilator lint_off WIDTHEXPAND
   always @(negedge clk) begin
      // Issue #5972
      reg_10[14:8] <= {1'b1, ~((in1[28:28] & ~(in1[28:28])))};
   end

   initial begin
      clk = 1;
      in1 = 1'b0;
      reg_10 = '0;
      #2;
      clk = 0;
      #2;
      `checkh(reg_10, 3);

      in1 = 1'b1;
      clk = 1;
      #2;
      clk = 0;
      #2;
      `checkh(reg_10, 3);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
