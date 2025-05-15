// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   z, z2, z3, z4, z5, z6, r,
   // Inputs
   a, b, ua, ub
   );

   input signed [170*32 : 0] a;
   input signed [170*32 : 0] b;
   input [170*32 : 0] ua;
   input [170*32 : 0] ub;

   output signed [170*32 : 0] z;
   output signed [170*32 : 0] z2;
   output signed [170*32 : 0] z3;
   output signed [170*32 : 0] z4;
   output [170*32 : 0] z5;
   output [170*32 : 0] z6;
   output real r;

   assign z = a * b;
   assign z2 = a ** 3;
   assign z3 = a / b;
   assign z4 = a % b;
   assign z5 = ua / ub;
   assign z6 = ua % ub;

   assign r = real'(a);

endmodule