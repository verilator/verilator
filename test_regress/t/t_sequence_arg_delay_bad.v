// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a, b;
  int n = 1;

  sequence seq_delay(logic sig1, logic sig2, int dly);
    sig1 ##dly sig2;
  endsequence
  sequence seq_range(logic sig1, logic sig2, int lo, int hi);
    sig1 ##[lo:hi] sig2;
  endsequence
  sequence seq_sum(logic sig1, logic sig2, int dly);
    sig1 ##(dly + n) sig2;
  endsequence
  property prop_delay(untyped dly);
    @(posedge clk) a |-> ##dly b;
  endproperty

  // The actual argument of a formal argument used as a cycle delay is not an elaboration-time
  // constant (IEEE 1800-2023 16.8)
  assert property (@(posedge clk) seq_delay(a, b, n));
  assert property (prop_delay(n));
  // The delays with the actual arguments are not valid (IEEE 1800-2023 16.7)
  assert property (@(posedge clk) seq_delay(a, b, -1));
  assert property (@(posedge clk) seq_range(a, b, 3, 1));
  assert property (@(posedge clk) seq_sum(a, b, 1));

endmodule
