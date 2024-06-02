// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   cnt0, cnt1,
   // Inputs
   clk, clk1
   );
   input clk;
   input clk1;

   output int cnt0;
   output int cnt1;

   always @ (posedge clk) cnt0 <= cnt0 + 1;
   always @ (posedge clk1) cnt1 <= cnt1 + 1;

   final if (cnt0 == 0) $stop;
   final if (cnt1 != 0) $stop;

   // Some dummy statements to make the code larger
   generate
      genvar  i;
      for (i = 0 ; i < 100; i = i + 1) begin
         always @(posedge clk) $c("/*", i, "*/");
      end
   endgenerate

   always_comb begin
      if (cnt0==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
