// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  sub s ();
  assign s.a[0] = 0;
  assign s.b[1] = 1;

  initial begin
    if (s.a != 2) $stop;
    if (s.b != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;

  end
endmodule

module sub;
  wire [1:0] a, b;
  alias a = b;
endmodule
