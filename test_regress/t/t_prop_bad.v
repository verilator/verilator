// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic a = 1'b1;
  logic b = 1'b1;
  logic c = 1'b1;

  assert property (@(posedge clk) weak (s_eventually a));
  assert property (@(posedge clk) weak (s_always[1: 2] a));
  assert property (@(posedge clk) weak (nexttime a));
  assert property (@(posedge clk) weak (s_nexttime a));
  assert property (@(posedge clk) weak (always a));
  assert property (@(posedge clk) weak (eventually[1: 2] a));
  assert property (@(posedge clk) weak (a |-> b));
  assert property (@(posedge clk) weak (a |=> b));
  assert property (@(posedge clk) weak (a implies b));
  assert property (@(posedge clk) weak (a iff b));
  assert property (@(posedge clk) weak (accept_on (a) b));
  assert property (@(posedge clk) weak (reject_on (a) b));
  assert property (@(posedge clk) weak(if (a) b else c));
  assert property (@(posedge clk) weak (strong (a)));
  assert property (@(posedge clk) strong (weak (a)));
endmodule
