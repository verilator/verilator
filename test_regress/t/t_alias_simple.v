// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  wire [15:0] a, b, c;
  wire [1:0] x, y;

  integer cyc = 0;

  alias a = b = c;
  assign a = 16'habcd;

  alias x = y;
  assign x[0] = 0;
  assign y[1] = 1;

  sub s ();

  initial begin
    if (a != 16'habcd) $stop;
    if (b != 16'habcd) $stop;
    if (c != 16'habcd) $stop;

    if (x != 2) $stop;
    if (y != 2) $stop;

    if (s.a != 1) $stop;
    if (s.b != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;

  end
endmodule

module sub;
  wire a, b;
  assign a = 1;
  alias a = b;
endmodule
;
