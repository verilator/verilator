// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts that a force or release whose left-hand side is automatically
// allocated storage reports an error citing IEEE 1800-2023 6.21, for each of a
// class property, an associative array element, a dynamic array element, and a
// queue element.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;

  class C;
    int a;
  endclass

  C c;
  int aa[int];
  int dyn[];
  int q[$];

  initial begin
    c = new;
    dyn = new[3];
    force c.a = 2;
    force aa[0] = 1;
    force dyn[0] = 1;
    force q[0] = 1;
    release c.a;
  end

endmodule
