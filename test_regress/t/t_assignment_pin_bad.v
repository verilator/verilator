// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module test2 (
    input logic b
);
  logic do_something;
  assign do_something = b;
endmodule

module test (
    input logic a[2]  // unpacked array
);

  logic b[2];

  assign b = a;

  test2 i_test2 (.b);

endmodule
