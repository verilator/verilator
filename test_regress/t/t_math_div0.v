// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(y, y2);
   output [3:0] y;
   output [31:0] y2;
   // bug775
   // verilator lint_off WIDTH
   assign y = ((0/0) ? 1 : 2) % 0;

   // bug2460
   reg [31:0]    b;
   assign y2 = $signed(32'h80000000) / $signed(b);

   initial begin
      b = 32'hffffffff;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
