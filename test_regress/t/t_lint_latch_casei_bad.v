// DESCRIPTION: Verilator: Verilog Test module for Issue#1609
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input a,
    output reg o
);

  always_comb begin
    // verilator lint_off CASEINCOMPLETE
    case (a)
      1'b0: o = 1;
    endcase
  end

endmodule
