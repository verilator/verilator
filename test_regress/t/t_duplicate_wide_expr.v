// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

localparam N = 100; // Should be wide

module t(i, o, o_single, o_outside);
   input i;
   wire [N-1:0] i;
   output o;
   wire [N-1:0][1:0] o;
   output o_single;
   wire [N-1:0] o_single;
   output o_outside;
   logic [N-1:0] o_outside;

   // Shouldn't be inlined
   wire [N-1:0] wide_non_simple = N << i;

   // Should be inlined
   wire [N-1:0] wide_const = 1 >> (N-1);
   wire [N-1:0] wide_single = N << i;
   wire [N-1:0] wide_outside = N ~^ i;

   for (genvar n = 0; n < N ; ++n) begin
      assign o[n][0] = i[N-1-n] | wide_non_simple[N-1-n];
      assign o[n][1] = i[N-1-n] & wide_const[N-1-n];
   end

   assign o_single = i ~| wide_single;

   sub sub(.i(i), .wide_outside(wide_outside), .o_outside(o_outside));
endmodule

module sub(input wire [N-1:0] i, input wire [N-1:0] wide_outside, output logic [N-1:0] o_outside);
   initial begin
      for (integer n = 0; n < N ; ++n) begin
         o_outside[n] = i[N-1-n] | wide_outside[N-1-n];
      end
   end
endmodule
