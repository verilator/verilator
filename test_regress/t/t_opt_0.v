// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  for (genvar k = 0; k < 1; k++) begin : gen_empty
    // empty
  end
  initial for (int i = 0; i < 1; i++) begin : gen_i
    // empty
  end
endmodule
