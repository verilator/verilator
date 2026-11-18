// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
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

  // Immediate assertion expressions are not property or sequence expressions
  always @(posedge clk) begin
    assert ($future_gclk(a) == a);
    assume ($rising_gclk(a));
    cover ($falling_gclk(a));
    assert #0 ($steady_gclk(a));
    assert final ($changing_gclk(a));
  end

  // A $cast task argument is not a property or sequence expression
  typedef enum logic {E0} e_t;
  e_t e;
  always @(posedge clk) $cast(e, $future_gclk(a));

  initial $stop;

endmodule
