// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

module t;
   timeunit 1ns;
   timeprecision 1ps;
   logic clkb, clk;

   initial begin
      clkb = 0;
   end

   always @(clk) begin
      clkb <= ~clk;
   end

   bot bot (.clkb(clkb), .clk(clk));

   final begin
      $display("[%g] final (%m)", $realtime());
   end
endmodule

module bot (input logic clkb, output logic clk);
   timeunit 1s;
   timeprecision 1fs;
   integer count;
   real    delay;

   initial begin
      count = 0;
      delay = 500e-9;
      clk = clkb;
      #(3.5 * delay) $display("[%g] Initial finishing, clkb = %b", $realtime(), clkb);
   end

   always @(clkb) begin
      $display("[%g] clkb is %b", $realtime(), clkb);
      count++;
      #(delay) clk = clkb;
   end

   always @(count) begin
      if (count > 20) begin
         $display("[%g] Finishing (%m)", $realtime());
         if ($realtime() < (delay * 20)) begin
            $display("[%g] %%Error: That was too quick!", $realtime());
         end
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   final begin
      $display("[%g] final (%m) count was %0d", $realtime(), count);
   end

endmodule
