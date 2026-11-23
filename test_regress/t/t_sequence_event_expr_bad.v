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
  int n1 = 0;
  int n2 = 0;

  sequence s_bool(x, y);
    x && y;
  endsequence
  sequence s_cycles(x);
    x ##1 x;
  endsequence
  sequence s_clocking(x, y);
    x || y;
  endsequence
  sequence s_disable(x, y);
    x && !y;
  endsequence

  // A sequence instance may not be an iff condition or a disable condition (IEEE 1800-2023 16.8)
  always @(posedge clk iff s_bool(a, b)) n1 <= n1 + 1;
  always @(posedge clk iff s_cycles(a)) n2 <= n2 + 1;
  clocking cb @(posedge clk iff s_clocking(a, b));
  endclocking
  default disable iff (s_disable(a, b));

  // Applies the default disable iff, other simulators only check it then
  assert property (@(posedge clk) a |-> b);

  // A property instance may not be an event expression (IEEE 1800-2023 16.12)
  property p_event(x);
    x;
  endproperty
  int n3 = 0;
  always @(p_event(a)) n3 <= n3 + 1;

  // A sequence or property instance may not be a constraint (IEEE 1800-2023 16.8, 16.12)
  class Cls;
    rand bit v;
    constraint c_seq {s_bool(v, v);}
    constraint c_prop {p_event(v);}
  endclass

  // Nor anywhere else but in the property expression of an assertion (IEEE 1800-2023 16.8)
  int n4 = 0;
  always @(posedge clk) if (s_bool(a, b)) n4 <= n4 + 1;
  assert property (@(posedge clk) disable iff (s_disable(a, b)) a);
  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence s_iff_clock;
    @(posedge clk iff s_bool(a, b)) a;
  endsequence
  // verilog_format: on
  assert property (s_iff_clock);
endmodule
