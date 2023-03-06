// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, a, b
   );

   input clk;
   int   a;
   int   b;
   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
   end

   // NOTE this grammar hasn't been checked with other simulators,
   // is here just to avoid uncovered code lines in the grammar.
   // NOTE using 'property weak' here as sequence/endsequence not supported
   property s_within;
      weak(a within(b));
   endproperty

   property s_and;
      weak(a and b);
   endproperty

   property s_or;
      weak(a or b);
   endproperty

   property s_throughout;
      weak(a throughout b);
   endproperty

   property s_intersect;
      weak(a intersect b);
   endproperty

   always @(posedge clk) begin
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
