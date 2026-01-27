// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  for (genvar k = 0; k < 1; k++) begin : gen_empty
    // empty
  end
  initial
    for (int i = 0; i < 1; i++) begin : gen_i
      // empty
    end
endmodule
