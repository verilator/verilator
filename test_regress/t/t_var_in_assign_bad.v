// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   value
   );
   input [3:0] value;
   assign      value = 4'h0;
   sub sub(.valueSub(value[3:0]));
endmodule

module sub (/*AUTOARG*/
   // Inputs
   valueSub
   );
   input [3:0] valueSub;
   assign      valueSub = 4'h0;
endmodule
