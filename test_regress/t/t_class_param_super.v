// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class base #(
    type T = int
);
  function void fbase();
  endfunction
endclass

class ext extends base;
  function void fext();
    super.fbase();
  endfunction
endclass
