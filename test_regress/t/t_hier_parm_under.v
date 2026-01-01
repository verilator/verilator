// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub;
  /* verilator hier_block */
  parametrized #(.ARG(1)) parametrized1 ();
  parametrized #(.ARG(2)) parametrized2 ();

  initial begin
    if (parametrized1.ARG != 1) $stop;
    if (parametrized2.ARG != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module parametrized #(
    parameter ARG = 0
);
  // This is a parametrized non-hier block under a hier block
endmodule

module t;
  sub sub ();
endmodule
