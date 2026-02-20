// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
class C;
  covergroup embedded(int x) with function sample (int a, bit b);
  endgroup
  function new();
    embedded = new(1);
    embedded.sample(2, 1'b0);
  endfunction
endclass
