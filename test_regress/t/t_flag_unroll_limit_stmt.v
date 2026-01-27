// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    // verilator unroll_full
    for (int i = 0; i < 4; ++i) begin
      $display("Should unroll: %0d", i);
    end

    // verilator unroll_full
    for (int i = 0; i < 5; ++i) begin
      $display("Should NOT unroll: %0d", i);
    end
  end

endmodule
