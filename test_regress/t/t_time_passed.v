// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   time    in;
   // verilator lint_off REALCVT
   initial in = 5432109876.543210ns;  // Will round to time units
   // verilator lint_on REALCVT

   // This shows time changes when passed between modules with different units
   // See also discussion in uvm_tlm2_time.svh

   ps ps (.*);
   ns ns (.*);

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 60) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

`timescale 1ps/1ps

module ps
  (input clk,
   input integer cyc,
   input time in);

   always @ (posedge clk) begin
      if (cyc == 10) begin
         $timeformat(-9, 6, "ns", 16);
         $write("%m: Input time %t %d\n", in, in);
      end
   end
endmodule

`timescale 1ns/1ps

module ns
  (input clk,
   input integer cyc,
   input time in);

   always @ (posedge clk) begin
      if (cyc == 20) begin
         $timeformat(-9, 6, "ns", 16);
         $write("%m: Input time %t %d\n", in, in);
      end
   end
endmodule
