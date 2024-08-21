// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (input signed [3:0] i4,
   output signed [2:0] ol3,
   output signed [3:0] ol4,
   output signed [4:0] ol5,
   output signed [2:0] or3,
   output signed [3:0] or4,
   output signed [4:0] or5,
   output signed [2:0] os3,
   output signed [3:0] os4,
   output signed [4:0] os5);

   assign ol3 = i4 << 1;  // WIDTHTRUNC
   assign ol4 = i4 << 1;
   assign ol5 = i4 << 1;  // WIDTHEXPAND, but ok due to shift amount 1

   assign or3 = i4 >> 1;  // WIDTHTRUNC, currently warn, but in future ok due to shift amount 1?
   assign or4 = i4 >> 1;
   assign or5 = i4 >> 1;  // WIDTHEXPAND

   assign os3 = i4 >>> 1;  // WIDTHTRUNC, currently warn, but in future ok due to shift amount 1?
   assign os4 = i4 >>> 1;
   assign os5 = i4 >>> 1;  // WIDTHEXPAND

endmodule
