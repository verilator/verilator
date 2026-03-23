// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// Assignment compatibility test.
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic a = 'z;
  logic b;

  assign b = ~a;

  initial begin
    #1;
    if (b !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
