// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  for (genvar i = 0; i < 4; ++i) begin
    initial $display("Should unroll: %0d", i);
  end

  for (genvar i = 0; i < 5; ++i) begin
    initial $display("Should NOT unroll: %0d", i);
  end

endmodule
