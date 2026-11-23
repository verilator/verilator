// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eduardo Schwarz Danni
// SPDX-License-Identifier: CC0-1.0

module t;
  int count = 0;
  int pause = 0;

  initial begin
    #5;
    count = 1;
    pause = count - 1;
    #(pause);
    count = 2;
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
