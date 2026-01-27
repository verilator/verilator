// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int x;

  function bit foo;
    x += 1;
    return bit'(x % 2);
  endfunction

  always @(posedge foo());

endmodule
