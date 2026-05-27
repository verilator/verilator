// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zhi QU
// SPDX-License-Identifier: CC0-1.0

module t;

  logic a;

  initial a = 1'b0;

  always_ff @(posedge a) begin
    a <= 1'b1;  // <--- Warning
  end

  logic b;

  always_ff @(posedge b) begin
    b <= 1'b1;
  end

  initial b = 1'b0;  // <--- Warning

endmodule
