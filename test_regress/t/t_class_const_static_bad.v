// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  const int instconst;  // OK, assigned in constructor
  static const int sconst = 1;  // OK
  static const int bad1;  // BAD: static instance constant
  const static int bad2;  // BAD: static instance constant
  function new;
    instconst = 2;
  endfunction
endclass

module t;
endmodule
