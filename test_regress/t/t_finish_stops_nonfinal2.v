// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int cyc;
  event e;

  always @(e) begin
    $display("e=%0d", e.triggered);
    ->e;
    cyc = cyc + 1;
    if (cyc >= 10) begin
      $display("Fin");
      $finish;
    end
  end

  initial begin
    #1;
    ->e;
    #1;
  end

  final begin
    if (cyc != 10) $stop;
  end
endmodule
