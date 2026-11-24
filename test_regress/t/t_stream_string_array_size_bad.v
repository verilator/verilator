// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic [4095:0] q[$];
  string s;
  initial for (int i = 0; i < 262144; ++i) q.push_back('0);
  always @(posedge clk) begin
    // A stream of 2**30 bits reordered in slices of nearly that size is too wide for a string
    s = {<<1073741800{q}};
    if (s.len() != 0) $stop;
    $stop;
  end
endmodule
