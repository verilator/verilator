// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire i
);

  wire [119:0] o;
  string s;
  logic [31:0] v;
  real r;

  assign o = string'(i ? "a" : "b");

  initial begin
    s = "a";
    v = s;
    v = signed'(s);
    r = s;
    $stop;
  end

endmodule
