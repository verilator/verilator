// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  global clocking @(posedge clk);
  endclocking

  int cyc = 0;
  logic [4:0] val = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    val = ~val;
  end

  property check(cyc_mod_2, untyped expected);
    @(posedge clk) cyc % 2 == cyc_mod_2 |=> val == expected;
  endproperty

  property sampled_values(signal);
    @(posedge clk) ($changed(signal) == $changed(cyc))
    && ($changed_gclk(signal) == $changed_gclk(cyc))
    && ($changing_gclk(signal) == $changing_gclk(cyc))
    && ($falling_gclk(signal) == $falling_gclk(cyc))
    && ($fell(signal) == $fell(cyc))
    && ($fell_gclk(signal) == $fell_gclk(cyc))
    && ($future_gclk(signal) == $future_gclk(cyc))
    && ($past(signal) == $past(cyc))
    && ($past_gclk(signal) == $past_gclk(cyc))
    && ($rising_gclk(signal) == $rising_gclk(cyc))
    && ($rose(signal) == $rose(cyc))
    && ($rose_gclk(signal) == $rose_gclk(cyc))
    && ($sampled(signal) == $sampled(cyc))
    && ($stable(signal) == $stable(cyc))
    && ($stable_gclk(signal) == $stable_gclk(cyc))
    && ($steady_gclk(signal) == $steady_gclk(cyc));
  endproperty

  assert property (sampled_values(cyc));

  assert property (check(0, 5'b11111))
  else begin
    // Assertion should pass
    $display("[%0t] Assert failed, but shouldn't", $time);
    $stop;
  end

  always @(posedge clk) begin
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
