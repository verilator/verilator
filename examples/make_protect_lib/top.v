// DESCRIPTION: Verilator: --protect-lib example module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// See also https://verilator.org/guide/latest/examples.html"

module top (input clk);

   integer cyc = 0;
   logic [31:0] a = 0;
   logic [31:0] b = 0;
   logic [31:0] x;

   verilated_secret secret (.a, .b, .x, .clk);

   always @(posedge clk) begin
      $display("[%0t] cyc=%0d a=%0d b=%0d x=%0d", $time, cyc, a, b, x);
      cyc <= cyc + 1;
      if (cyc == 0) begin
         a <= 5;
         b <= 7;
      end else if (cyc == 1) begin
         a <= 6;
         b <= 2;
      end else if (cyc == 2) begin
         a <= 1;
         b <= 9;
      end else if (cyc > 3) begin
         $display("Done");
         $finish;
      end
   end

endmodule
