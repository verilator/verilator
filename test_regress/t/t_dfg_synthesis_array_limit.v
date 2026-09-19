// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t #(
    parameter int N = 256
) (
    input logic [7:0] i[N],
    output logic [7:0] o[N]
);
  always_comb begin
    /*verilator unroll_full*/
    for (int k = 0; k < N; ++k) o[k] = i[k];
  end
endmodule
