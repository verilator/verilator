// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input in
);

  // A typed formal may not be assigned (IEEE 1800-2023 16.8.1)
  sequence s_typed(int x);
    (1, x = 1);
  endsequence

  // A module input may not be assigned
  sequence s_input;
    (1, in = 1);
  endsequence

  assert property (@(posedge clk) s_typed(1));
  assert property (@(posedge clk) s_input);
endmodule
