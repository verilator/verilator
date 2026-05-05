// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  always #1 clk = ~clk;

  bit c_true = 1'b1;
  bit c_false = 1'b0;
  bit b = 1'b0;
  bit c = 1'b0;
  bit [3:0] vec = 4'b1110;

  initial begin
    #20 $write("*-* All Finished *-*\n");
    $finish;
  end

  // Simple boolean `!` as the rhs of ##1.
  property p_bang_simple;
    @(posedge clk) c_true ##1 !c_false;
  endproperty
  ap_bang_simple :
  assert property (p_bang_simple);

  // Conjunction of two bangs inside the sequence.
  property p_bang_and;
    @(posedge clk) c_true ##1 (!b && !c);
  endproperty
  ap_bang_and :
  assert property (p_bang_and);

  // Bit-select negation.
  property p_bang_bit;
    @(posedge clk) c_true ##1 !vec[0];
  endproperty
  ap_bang_bit :
  assert property (p_bang_bit);

  // Sampled value function inside a negation.
  property p_bang_past;
    @(posedge clk) c_true ##1 !$past(
        c_false
    );
  endproperty
  ap_bang_past :
  assert property (p_bang_past);

  // Bang interleaved with multiple cycle delays.
  property p_bang_interleaved;
    @(posedge clk) c_true ##0 !c_false ##1 c_true;
  endproperty
  ap_bang_interleaved :
  assert property (p_bang_interleaved);

  // CVV-style: bang on the consequent of an implication, mirroring
  // core-v-verif's `|-> ##1 !irq_enabled` pattern that motivated this fix.
  property p_bang_cvv_style;
    @(posedge clk) c_true |-> ##1 !c_false;
  endproperty
  ap_bang_cvv_style :
  assert property (p_bang_cvv_style);

endmodule
