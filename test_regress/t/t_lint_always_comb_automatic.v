// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic a,
    input logic [7:0] b,
    output logic [7:0] c
);

  always_comb begin : p
    c = b;
    if (a) begin : x
      automatic logic [7:0] n;
      n = b;
      n += 8'h01;
      c = n;
    end
  end
endmodule
