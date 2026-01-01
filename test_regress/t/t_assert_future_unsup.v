// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input a,
    input clk
);

  function logic func(input logic i);
    return i;
  endfunction

  global clocking @(posedge clk);
  endclocking

  assert property (@(posedge clk) $future_gclk(a) == func(a));

endmodule
