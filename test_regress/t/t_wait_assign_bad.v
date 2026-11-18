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
    wait ((foo += bar) == 23);
    wait (((foo = bar) == 1) && ((foo -= 1) != 0));
    // verilator lint_on ASSIGNEQEXPR
    wait (foo++ == 23);
    wait (foo-- == 23);
    wait (++foo == 23);
    wait (--foo);
  endtask

endmodule
