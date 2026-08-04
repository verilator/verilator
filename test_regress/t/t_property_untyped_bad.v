// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  global clocking @(posedge clk);
  endclocking

  int values[2];

  property sampled_values(signal);
    @(posedge clk) $changed(signal)
    && $changed_gclk(signal)
    && $changing_gclk(signal)
    && $falling_gclk(signal)
    && $fell(signal)
    && $fell_gclk(signal)
    && $future_gclk(signal)
    && $past(signal)
    && $past_gclk(signal)
    && $rising_gclk(signal)
    && $rose(signal)
    && $rose_gclk(signal)
    && $sampled(signal)
    && $stable(signal)
    && $stable_gclk(signal)
    && $steady_gclk(signal);
  endproperty

  assert property (sampled_values(values));
endmodule
