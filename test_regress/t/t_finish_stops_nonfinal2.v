// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  event e;
  logic [1:0] x = 0;

  always @ (e) begin
    ->e;
    x <= 1;
    $display("Fin");
    $finish;
    x = 2;
  end

  final begin
    $display("Final x=%0d", x);
    assert (x == 1);
  end

  initial ->e;
endmodule
