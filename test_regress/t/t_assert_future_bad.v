// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input a,
    input clk
);

  global clocking @(posedge clk);
  endclocking

  assert property (@(posedge clk) 1 == 1)
  else $display("Future=%0d", $future_gclk(a));

  assert property (@(posedge clk) 1 == 1)
  else $display("Future=%0d", $rising_gclk(a));

  assert property (@(posedge clk) 1 == 1)
  else $display("Future=%0d", $falling_gclk(a));

  assert property (@(posedge clk) 1 == 1)
  else $display("Future=%0d", $steady_gclk(a));

  assert property (@(posedge clk) 1 == 1)
  else $display("Future=%0d", $changing_gclk(a));

  initial $stop;

endmodule
