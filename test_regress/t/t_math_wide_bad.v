// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   z, z2, r,
   // Inputs
   a, b
   );

   input signed [17*32 : 0] a;
   input signed [17*32 : 0] b;

   output signed [17*32 : 0] z;
   output signed [17*32 : 0] z2;
   output real r;

   assign z = a * b;
   assign z2 = a ** 3;
   assign r = real'(a);

endmodule
