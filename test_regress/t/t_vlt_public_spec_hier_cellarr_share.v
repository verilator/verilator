// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


// Demonstrate that per-instance selectivity is NOT yet implemented for
// arrayed cells.

module sub();
  int leaf = 0;
endmodule

module top();
  sub i_sub [1:0] ();

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
