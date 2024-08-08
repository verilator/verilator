// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   integer      cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   mid mid_a(clk);
   mid mid_b(clk);
   mid mid_c(clk);
endmodule

module mid(input wire clk);
   int cnt = 0;
   always @(posedge clk) cnt += 1;
   sub sub_a(clk);
   sub sub_b(clk);
   sub sub_c(clk);
endmodule

module sub(input wire clk);
   int cnt = 0;
   always @(posedge clk) cnt += 2;
endmodule
