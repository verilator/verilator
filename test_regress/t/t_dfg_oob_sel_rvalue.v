// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t (
    input logic [0:0][2:0] i,
    output logic o
);

  always_comb begin
    o = 1'b0;
    // verilator unroll_full
    for (int n = 0; n < 3; ++n) begin
      o = o | i[n] == 3'd0;  // Intentionally out of bounds
    end
  end

endmodule
