// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (
   output reg [1020:0] res1,
   output reg [1020:0] res2,
   output reg [1022:0] res3,
   output reg [1022:0] res4
   );
   always_inline always_inline(res1, res2);
   dont_inline dont_inline(res3, res4);
endmodule

module always_inline(
   output reg [1020:0] res1,
   output reg [1020:0] res2
   );

   wire [1023:0] a;
   wire [478:0] b;

   assign b = a[510:32];
   assign res1  = {542'b0, b};
   assign res2 = {542'b1, b};
endmodule

// SEL does not have proper offset so we do not have guarantee that it will be
// emitted as '[' operator, thus we do not exclude it from inlining.
module dont_inline(
   output reg [1022:0] res1,
   output reg [1022:0] res2
   );

   wire [1023:0] a;
   wire [480:0] b;

   // LSB % 32 != 0
   assign b = a[510:30];
   assign res1  = {542'b0, b};
   assign res2 = {542'b1, b};
endmodule
