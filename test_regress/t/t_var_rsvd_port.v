// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2005 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    bool
);

  input bool;  // BAD

  reg vector;  // OK, as not public
  reg switch  /*verilator public_flat*/;  // Bad
  reg free  /*verilator public_flat*/;  // OK, not actually a keyword

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
