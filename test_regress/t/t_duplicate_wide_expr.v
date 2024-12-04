// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

localparam N = 256; // Wider than expand limit.

module t(
   clk,
   i,
   o,
   o_assign,
   o_single,
   o_outside,
   o_non_blocking,
   o_sel,
   o_swizzle,
   o_small,
   o_multiple1,
   o_multiple2
   );
   input clk;
   input wire [N-1:0] i;
   output wire [N-1:0][2:0] o;
   output wire [N-1:0] o_single;
   output logic [N-1:0] o_outside;
   output logic [N:0] o_multiple1;
   output logic [N:0] o_multiple2;
   output logic [N-1:0] o_sel;
   output logic [N-1:0] o_assign;
   output logic [N-1:0] o_non_blocking;
   output logic [N:0] o_swizzle;
   output logic [65:0] o_small;

   // Shouldn't be inlined
   wire [N-1:0] wide_non_simple = N << i;
   wire [N:0] wide_multiple = N >> i;

   // Should be inlined
   wire [N-1:0] wide_const_expr = 1 >> (N-1);
   wire [N-1:0] wide_const = 256'h1234_5678_aaaa_bbbb;
   wire [N-1:0] wide_single = N << i;
   wire [N-1:0] wide_outside = N ~^ i;
   wire [N-1:0] wide_assign = i;
   wire [N-1:0][2:0] wide_assign_dim;
   wire [N:0][N:0] wide_swizzle = 66049'(N & i);
   wire [65:0] wide_small = N << i * i / N;

   assign wide_assign_dim = o;
   for (genvar n = 0; n < N - 1; ++n) begin
      assign o[n][0] = i[N-1-n] | wide_non_simple[N-1-n];
      assign o[n][1] = i[N-1-n] & wide_const_expr[N-1-n];
      assign o[n][2] = i[N-1-n] ~& wide_const[N-1-n];
      assign o_assign[n] = wide_assign[N-1-n];
      assign o_swizzle[n] = 1'(wide_swizzle[n][n+1:n]);
   end

   for (genvar n = 0; n < 65; ++n) begin
      assign o_small[n] = i[n] ^ wide_small[n];
   end

   for (genvar n = 0; n < N; ++n) begin
      always @(posedge clk) begin
         o_non_blocking[n] <= wide_const[N-1-n] & wide_non_simple[N-1-n];
      end
   end

   assign o_single = i ~| wide_single;
   assign o_multiple1 = wide_multiple | i + 1;
   assign o_multiple2 = wide_multiple | i + 2;

   sub sub(.i(i), .wide_outside(wide_outside), .o_outside(o_outside));
endmodule

module sub(input wire [N-1:0] i, input wire [N-1:0] wide_outside, output logic [N-1:0] o_outside);
   initial begin
      for (integer n = 0; n < N ; ++n) begin
         o_outside[n] = i[N-1-n] | wide_outside[N-1-n];
      end
   end
endmodule
