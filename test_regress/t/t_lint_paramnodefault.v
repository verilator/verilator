// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub;
  parameter NODEF;  //<--- Warning
  initial begin
    if (NODEF != 6) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module t;
  sub #(6) sub();
endmodule
