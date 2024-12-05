// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

localparam N = 256; // Wider than expand limit.

module t(
   input wire [N-1:0] i,
   output logic [N-1:0] o_multiple1,
   output logic [N-1:0] o_multiple2,
   output wire [N-1:0] o
   );

   // Exclude from inline wide expressions referenced multiple times.
   wire [N-1:0] wide_multiple_assigns = N >> i;
   wire [N-1:0] wide = N << i;

   for (genvar n = 0; n < N - 1; ++n) begin
      assign o[n] = i[N-1-n] | wide[N-1-n];
   end

   assign o_multiple1 = wide_multiple_assigns | i + 1;
   assign o_multiple2 = wide_multiple_assigns | i + 2;
endmodule

