// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic [6:0] a,
    input logic b,
    output logic c
);
  assign c = ({a, b} == 8'h00);

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
