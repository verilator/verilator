// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Saqib Khan
// SPDX-License-Identifier: CC0-1.0

module child #(
    parameter int W = 1
);
  typedef enum logic [4:0] {
    S_IDLE = 0,
    S_WORK = 5'(W)
  } state_t;
endmodule

module t;
  for (genvar g = 0; g < 2; ++g) begin : gen
    child #(.W(g + 4)) u ();
  end
  int bad = int'(gen[2].u.S_WORK);
endmodule
