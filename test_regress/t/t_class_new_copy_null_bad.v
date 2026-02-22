// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Base;
  int value;
endclass

module t;
  Base b;
  Base a;
  initial begin
    b = null;
    a = new b;  // BAD: null handle dereference (IEEE 8.7)
    if (a != null) $write("unexpected clone\n");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
