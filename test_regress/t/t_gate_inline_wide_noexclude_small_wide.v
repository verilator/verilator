// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

localparam N = 65; // Wide but narrower than expand limit

module t(
   input wire [N-1:0] i,
   output wire [N-1:0] o
   );

   // Do not exclude from inlining wides small enough to be handled by
   // V3Expand.
   wire [65:0] wide_small = N << i * i / N;

   for (genvar n = 0; n < N; ++n) begin
      assign o[n] = i[n] ^ wide_small[n];
   end
endmodule
