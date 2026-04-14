// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Power (**) with constant non-2 base and non-constant exponent is unsupported.
// Only base 2 can be lowered to SMT via left-shift; other bases have no SMT encoding.
class C;
  rand int unsigned n;
  rand int unsigned x;
  constraint c { x == 3 ** n; }
endclass

module t;
  C obj;
  initial begin
    obj = new;
    void'(obj.randomize());
    $finish;
  end
endmodule
