// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input a,
    input b
);
  localparam int unsigned MAX_SUPPORTED = 32'h7fffffdf;  // INT_MAX - 32

  default clocking cb @(posedge clk);
  endclocking

  sequence s_fixed; a ##MAX_SUPPORTED b; endsequence

  sequence s_range_hi; a ##[0:MAX_SUPPORTED] b; endsequence

  sequence s_range_lo; a ##[MAX_SUPPORTED:$] b; endsequence

  sequence s_intersect;
    (a ##MAX_SUPPORTED b ##4 a) intersect (a ##MAX_SUPPORTED b ##4 a);
  endsequence

  sequence s_within; a within (a ##MAX_SUPPORTED b); endsequence

  sequence s_past;
    $past(
        a, MAX_SUPPORTED
    );
  endsequence

  property p_always_hi;
    always[0: MAX_SUPPORTED] a;
  endproperty

  property p_always_lo;
    always[MAX_SUPPORTED: $] a;
  endproperty

  property p_s_always_hi;
    s_always[0: MAX_SUPPORTED] a;
  endproperty

endmodule
