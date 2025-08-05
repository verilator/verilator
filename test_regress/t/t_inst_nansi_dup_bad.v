// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef int T;

module test (  /*AUTOARG*/
  // Outputs
  bad4, bad5
  );

  output bad4;
  reg bad4;
  reg bad4;  // <--- Error (duplicate)

  output bad5;
  output bad5;  // <--- Error (duplicate)
  reg bad5;  // <--- Error (duplicate)

endmodule
