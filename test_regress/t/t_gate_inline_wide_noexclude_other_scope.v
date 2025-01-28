// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

localparam N = 256; // Wider than expand limit.

module t(
   input wire [N-1:0] i,
   output wire [N-1:0] o
   );

   // Do not exclude from inlining wides referenced in different scope.
   wire [N-1:0] wide = N ~^ i;

   sub sub(i, wide, o);
endmodule

module sub(input wire [N-1:0] i, input wire [N-1:0] wide, output logic [N-1:0] o);
   initial begin
      for (integer n = 0; n < N ; ++n) begin
         o[n] = i[N-1-n] | wide[N-1-n];
      end
   end
endmodule
