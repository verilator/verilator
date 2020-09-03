// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   y, d2, m2, d3, m3
   );
   output [3:0] y;
   output [31:0] d2;
   output [31:0] m2;
   output [63:0] d3;
   output [63:0] m3;
   // bug775
   // verilator lint_off WIDTH
   assign y = ((0/0) ? 1 : 2) % 0;

   // bug2460
   reg [31:0]    b;
   assign d2 = $signed(32'h80000000) / $signed(b);
   assign m2 = $signed(32'h80000000) % $signed(b);
   reg [63:0]    b3;
   assign d3 = $signed(64'h80000000_00000000) / $signed(b3);
   assign m3 = $signed(64'h80000000_00000000) % $signed(b3);

   initial begin
      b = 32'hffffffff;
      b3 = 64'hffffffff_ffffffff;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
