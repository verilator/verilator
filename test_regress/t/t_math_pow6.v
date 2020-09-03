// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   i65, j65, i33, j33, i30, j30, q65, r65, q33, r33, q30, r30, w65, x65, w33,
   x33, w30, x30,
   // Inputs
   a, a40, a70
   );

   input [3:0] a;
   input [39:0] a40;
   input [69:0] a70;

   // -- Verilator 621c515 creates code that uses the undeclared function VL_POW_WWI()
   // verilator lint_off WIDTH
   output [3:0] i65 = 65'd3 ** a; // WWI
   output [3:0] j65 = a ** 65'd3; // IIW
   output [3:0] i33 = 33'd3 ** a; // QQI
   output [3:0] j33 = a ** 33'd3; // IIQ
   output [3:0] i30 = 30'd3 ** a; // III
   output [3:0] j30 = a ** 30'd3; // III

   output [39:0] q65 = 65'd3 ** a40; // WWQ
   output [39:0] r65 = a40 ** 65'd3; // WWQ
   output [39:0] q33 = 33'd3 ** a40; // QQQ
   output [39:0] r33 = a40 ** 33'd3; // QQQ
   output [39:0] q30 = 30'd3 ** a40; // QQI
   output [39:0] r30 = a40 ** 30'd3; // QQI

   output [69:0] w65 = 65'd3 ** a70; // WWW
   output [69:0] x65 = a70 ** 65'd3; // WWW
   output [69:0] w33 = 33'd3 ** a70; // WWW
   output [69:0] x33 = a70 ** 33'd3; // WWW
   output [69:0] w30 = 30'd3 ** a70; // WWW
   output [69:0] x30 = a70 ** 30'd3; // WWW
   // verilator lint_on WIDTH

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
