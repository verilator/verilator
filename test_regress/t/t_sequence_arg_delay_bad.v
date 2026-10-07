// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  bit a, b;
  int n = 1;
  int fails = 0;

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
  assert property (@(posedge clk) a |-> seq_delay(1'b1, b, n))
  else fails++;
  assert property (prop_delay(n))
  else fails++;
  // The delays with the actual arguments are not valid (IEEE 1800-2023 16.7)
  assert property (@(posedge clk) a |-> seq_delay(1'b1, b, -1))
  else fails++;
  assert property (@(posedge clk) a |-> seq_range(1'b1, b, 3, 1))
  else fails++;
  assert property (@(posedge clk) a |-> seq_sum(1'b1, b, 1))
  else fails++;

  // As 'a' is never set, none would fail
  final `checkd(fails, 0)

endmodule
