// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int bar;

  task one;
    int foo;
    // verilator lint_off ASSIGNEQEXPR
    wait ((foo = bar) == 23);
    // verilator lint_on ASSIGNEQEXPR
    wait ((foo += bar) == 23);
  endtask

endmodule
