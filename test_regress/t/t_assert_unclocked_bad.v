// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  logic a, b;
  assert property (a);
  assert property (a |=> b);
  assert property ((a [* 2]) implies (a [* 2]));
  assert property ((s_eventually a) implies (s_eventually a));
  assert property ((a s_until b) implies (a s_until b));
  assert property ((a until_with b) implies (a until_with b));
  assert property ((a s_until_with b) implies (a s_until_with b));
  assert property ((a |-> b) implies (a |-> b));
  assert property ((a #-# b) implies (a #-# b));
  assert property ((s_eventually a) iff (s_eventually a));
  assert property ((a s_until b) iff (a s_until b));
  assert property ((a until_with b) iff (a until_with b));
  assert property ((a s_until_with b) iff (a s_until_with b));
  assert property ((a |-> b) iff (a |-> b));
  assert property ((a #-# b) iff (a #-# b));
  cover property (a);
endmodule
