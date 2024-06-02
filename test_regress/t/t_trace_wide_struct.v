// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef struct {
       logic [64:0] long_signal;
   } mystruct_t;

   mystruct_t mystruct;

   initial begin
       $finish;
   end

endmodule
