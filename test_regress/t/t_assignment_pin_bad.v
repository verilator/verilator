// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module test1 (
    input logic b
);
  logic do_something;
  assign do_something = b;
endmodule

module test2 (
    input bit b[2]
);
  bit do_something[2];
  assign do_something = b;
endmodule

module t (
    input logic a[2]  // unpacked array
);

  logic b[2];

  assign b = a;

  test1 i_test1 (.b);
  test2 i_test2 (.b);

endmodule
