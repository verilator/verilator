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

  wire [31:0] a, b;
  wire [31:0] x, y;

  integer cyc = 0;

  alias a = b;
  assign a = cyc;

  alias x = y;
  assign x[15:0] = cyc[15:0];
  assign y[31:16] = cyc[31:16];

  sub s (cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (a != cyc) $stop;
    if (b != cyc) $stop;

    if (x != cyc) $stop;
    if (y != cyc) $stop;

    if (s.a != cyc) $stop;
    if (s.b != cyc) $stop;
    $write("*-* All Finished *-*\n");
    $finish;

  end
endmodule

module sub (
    input integer cyc
);
  wire [31:0] a, b;
  assign a = cyc;
  alias a = b;
endmodule
;
