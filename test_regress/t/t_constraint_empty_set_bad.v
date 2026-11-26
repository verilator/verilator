// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic a;
  initial begin
    // A procedural if body cannot be an empty brace block
    if (a) {}
  end
endmodule
